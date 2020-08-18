{-# language CPP, BangPatterns #-}

module GHC.CmmToAsm.AArch64.Instr

where

#include "HsVersions.h"

import GHC.Prelude

import GHC.CmmToAsm.AArch64.Cond
import GHC.CmmToAsm.AArch64.Regs

import GHC.CmmToAsm.Instr
import GHC.CmmToAsm.Format
import GHC.CmmToAsm.Reg.Target
import GHC.CmmToAsm.Config
import GHC.Platform.Reg.Class
import GHC.Platform.Reg

import GHC.Platform.Regs
import GHC.Cmm.BlockId
import GHC.Cmm.Dataflow.Collections
import GHC.Cmm.Dataflow.Label
import GHC.Cmm
import GHC.Cmm.Info
import GHC.Data.FastString
import GHC.Cmm.CLabel
import GHC.Utils.Outputable
import GHC.Platform
import GHC.Types.Unique.FM (listToUFM, lookupUFM)
import GHC.Types.Unique.Supply

import Control.Monad (replicateM)
import Data.Maybe (fromMaybe)

import Debug.Trace

-- | XXX: verify this!
stackFrameHeaderSize :: Platform -> Int
stackFrameHeaderSize _ = 64

-- | All registers are 8 byte wide.
spillSlotSize :: Int
spillSlotSize = 8

-- | The number of bytes that the stack pointer should be aligned
-- to.
stackAlign :: Int
stackAlign = 16

-- | The number of spill slots available without allocating more.
maxSpillSlots :: NCGConfig -> Int
maxSpillSlots config
--  = 0 -- set to zero, to see when allocMoreStack has to fire.
    = let platform = ncgPlatform config
      in ((ncgSpillPreallocSize config - stackFrameHeaderSize platform)
         `div` spillSlotSize) - 1

-- | Convert a spill slot number to a *byte* offset, with no sign.
spillSlotToOffset :: NCGConfig -> Int -> Int
spillSlotToOffset config slot
   = stackFrameHeaderSize (ncgPlatform config) + spillSlotSize * slot

-- | Instruction instance for powerpc
instance Instruction Instr where
        regUsageOfInstr         = aarch64_regUsageOfInstr
        patchRegsOfInstr        = aarch64_patchRegsOfInstr
        isJumpishInstr          = aarch64_isJumpishInstr
        jumpDestsOfInstr        = aarch64_jumpDestsOfInstr
        patchJumpInstr          = aarch64_patchJumpInstr
        mkSpillInstr            = aarch64_mkSpillInstr
        mkLoadInstr             = aarch64_mkLoadInstr
        takeDeltaInstr          = aarch64_takeDeltaInstr
        isMetaInstr             = aarch64_isMetaInstr
        mkRegRegMoveInstr _     = aarch64_mkRegRegMoveInstr
        takeRegRegMoveInstr     = aarch64_takeRegRegMoveInstr
        mkJumpInstr             = aarch64_mkJumpInstr
        mkStackAllocInstr       = aarch64_mkStackAllocInstr
        mkStackDeallocInstr     = aarch64_mkStackDeallocInstr

-- | Get the registers that are being used by this instruction.
-- regUsage doesn't need to do any trickery for jumps and such.
-- Just state precisely the regs read and written by that insn.
-- The consequences of control flow transfers, as far as register
-- allocation goes, are taken care of by the register allocator.
--
-- RegUsage = RU [<read regs>] [<write regs>]

instance Outputable RegUsage where
    ppr (RU reads writes) = text "RegUsage(reads:" <+> ppr reads <> comma <+> text "writes:" <+> ppr writes <> char ')'

aarch64_regUsageOfInstr :: Platform -> Instr -> RegUsage
aarch64_regUsageOfInstr platform instr = case instr of
  ANN _ i                  -> aarch64_regUsageOfInstr platform i
  -- 1. Arithmetic Instructions ------------------------------------------------
  ADD dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  ADDS dst src1 src2       -> usage (regOp src1 ++ regOp src2, regOp dst)
  CMN l r                  -> usage (regOp l ++ regOp r, [])
  CMP l r                  -> usage (regOp l ++ regOp r, [])
  MSUB dst src1 src2 src3  -> usage (regOp src1 ++ regOp src2 ++ regOp src3, regOp dst)
  MUL dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  NEG dst src              -> usage (regOp src, regOp dst)
  SDIV dst src1 src2       -> usage (regOp src1 ++ regOp src2, regOp dst)
  SUB dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  UDIV dst src1 src2       -> usage (regOp src1 ++ regOp src2, regOp dst)

  -- 2. Bit Manipulation Instructions ------------------------------------------
  SBFM dst src _ _         -> usage (regOp src, regOp dst)
  UBFM dst src _ _         -> usage (regOp src, regOp dst)

  -- 3. Logical and Move Instructions ------------------------------------------
  AND dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  ADDS dst src1 src2       -> usage (regOp src1 ++ regOp src2, regOp dst)
  ASR dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  BIC dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  BICS dst src1 src2       -> usage (regOp src1 ++ regOp src2, regOp dst)
  EON dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  EOR dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  LSL dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  LSR dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  MOV dst src              -> usage (regOp src, regOp dst)
  MOVK dst src             -> usage (regOp src, regOp dst)
  MVN dst src              -> usage (regOp src, regOp dst)
  ORR dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  ROR dst src1 src2        -> usage (regOp src1 ++ regOp src2, regOp dst)
  TST src1 src2            -> usage (regOp src1 ++ regOp src2, [])
  -- 4. Branch Instructions ----------------------------------------------------
  J t                      -> usage (regTarget t, [])
  B t                      -> usage (regTarget t, [])
  BCOND _ t                -> usage (regTarget t, [])
  BL t                     -> usage (regTarget t, callerSavedRegisters)

  -- 5. Atomic Instructions ----------------------------------------------------
  -- 6. Conditional Instructions -----------------------------------------------
  CSET dst _               -> usage ([], regOp dst)
  CBZ src _                -> usage (regOp src, [])
  CBNZ src _               -> usage (regOp src, [])
  -- 7. Load and Store Instructions --------------------------------------------
  STR _ src dst            -> usage (regOp src ++ regOp dst, [])
  LDR _ dst src            -> usage (regOp src, regOp dst)
  -- XXX is this right? see STR, which I'm only partial about being right?
  STP _ src1 src2 dst      -> usage (regOp src1 ++ regOp src2 ++ regOp dst, [])
  LDP _ dst1 dst2 src      -> usage (regOp src, regOp dst1 ++ regOp dst2)

  -- 8. Synchronization Instructions -------------------------------------------
  DMBSY                    -> usage ([], [])

  -- 9. Floating Point Instructions --------------------------------------------
  FCVT dst src             -> usage (regOp src, regOp dst)
  SCVTF dst src            -> usage (regOp src, regOp dst)
  FCVTZS dst src           -> usage (regOp src, regOp dst)

  _ -> panic "regUsageOfInstr"

  where
        -- filtering the usage is necessary, otherwise the register
        -- allocator will try to allocate pre-defined fixed stg
        -- registers as well, as they show up.
        usage (src, dst) = RU (filter (interesting platform) src)
                              (filter (interesting platform) dst)

        regAddr :: AddrMode -> [Reg]
        regAddr (AddrRegReg r1 r2) = [r1, r2]
        regAddr (AddrRegImm r1 _)  = [r1]
        regAddr (AddrReg r1)       = [r1]
        regOp :: Operand -> [Reg]
        regOp (OpReg _ r1) = [r1]
        regOp (OpRegExt _ r1 _ _) = [r1]
        regOp (OpRegShift _ r1 _ _) = [r1]
        regOp (OpAddr a) = regAddr a
        regOp (OpImm _) = []
        regOp (OpImmShift _ _ _) = []
        regTarget :: Target -> [Reg]
        regTarget (TBlock _) = []
        regTarget (TLabel _) = []
        regTarget (TReg r1)  = [r1]

        -- Is this register interesting for the register allocator?
        interesting :: Platform -> Reg -> Bool
        interesting _        (RegVirtual _)                 = True
        interesting platform (RegReal (RealRegSingle (-1))) = False
        interesting platform (RegReal (RealRegSingle i))    = freeReg platform i
        interesting _        (RegReal (RealRegPair{}))
            = panic "AArch64.Instr.interesting: no reg pairs on this arch"

-- Save caller save registers
-- This is x0-x18
--
-- For SIMD/FP Registers:
-- Registers v8-v15 must be preserved by a callee across subroutine calls;
-- the remaining registers (v0-v7, v16-v31) do not need to be preserved (or
-- should be preserved by the caller). Additionally, only the bottom 64 bits
-- of each value stored in v8-v15 need to be preserved [7]; it is the
-- responsibility of the caller to preserve larger values.
--
-- .---------------------------------------------------------------------------------------------------------------------------------------------------------------.
-- |  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 |
-- | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 | 42 | 44 | 45 | 46 | 47 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 | 58 | 59 | 60 | 61 | 62 | 63 |
-- |== General Purpose registers ==================================================================================================================================|
-- | <---- argument passing -------------> | IR | <------- tmp registers --------> | IP0| IP1| PL | <------------------- callee saved ------------> | FP | LR | SP |
-- | <------ free registers --------------------------------------------------------------------> | BR | Sp | Hp | R1 | R2 | R3 | R4 | R5 | R6 | SL | -- | -- | -- |
-- |== SIMD/FP Registers ==========================================================================================================================================|
-- | <---- argument passing -------------> | <-- callee saved (lower 64 bits) ---> | <--------------------------------------- caller saved ----------------------> |
-- | <------ free registers -------------> | F1 | F2 | F3 | F4 | D1 | D2 | D3 | D4 | <------ free registers -----------------------------------------------------> |
-- '---------------------------------------------------------------------------------------------------------------------------------------------------------------'
-- IR: Indirect result location register, IP: Intra-procedure register, PL: Platform register, FP: Frame pointer, LR: Link register, SP: Stack pointer
-- BR: Base, SL: SpLim
callerSavedRegisters :: [Reg]
callerSavedRegisters
    = map regSingle [0..18]
    ++ map regSingle [32..39]
    ++ map regSingle [48..63]

-- | Apply a given mapping to all the register references in this
-- instruction.
aarch64_patchRegsOfInstr :: Instr -> (Reg -> Reg) -> Instr
aarch64_patchRegsOfInstr instr env = case instr of
    -- 0. Meta Instructions
    ANN d i        -> ANN d (aarch64_patchRegsOfInstr i env)
    -- 1. Arithmetic Instructions ----------------------------------------------
    ADD o1 o2 o3   -> ADD (patchOp o1) (patchOp o2) (patchOp o3)
    ADDS o1 o2 o3  -> ADDS (patchOp o1) (patchOp o2) (patchOp o3)
    CMN o1 o2      -> CMN (patchOp o1) (patchOp o2)
    CMP o1 o2      -> CMP (patchOp o1) (patchOp o2)
    MSUB o1 o2 o3 o4 -> MSUB (patchOp o1) (patchOp o2) (patchOp o3) (patchOp o4)
    MUL o1 o2 o3   -> MUL (patchOp o1) (patchOp o2) (patchOp o3)
    NEG o1 o2      -> NEG (patchOp o1) (patchOp o2)
    SDIV o1 o2 o3  -> SDIV (patchOp o1) (patchOp o2) (patchOp o3)
    SUB o1 o2 o3   -> SUB  (patchOp o1) (patchOp o2) (patchOp o3)
    UDIV o1 o2 o3  -> UDIV (patchOp o1) (patchOp o2) (patchOp o3)

    -- 2. Bit Manipulation Instructions ----------------------------------------
    SBFM o1 o2 o3 o4 -> SBFM (patchOp o1) (patchOp o2) (patchOp o3) (patchOp o4)
    UBFM o1 o2 o3 o4 -> UBFM (patchOp o1) (patchOp o2) (patchOp o3) (patchOp o4)

    -- 3. Logical and Move Instructions ----------------------------------------
    AND o1 o2 o3   -> AND  (patchOp o1) (patchOp o2) (patchOp o3)
    ANDS o1 o2 o3  -> ANDS (patchOp o1) (patchOp o2) (patchOp o3)
    ASR o1 o2 o3   -> ASR  (patchOp o1) (patchOp o2) (patchOp o3)
    BIC o1 o2 o3   -> BIC  (patchOp o1) (patchOp o2) (patchOp o3)
    BICS o1 o2 o3  -> BICS (patchOp o1) (patchOp o2) (patchOp o3)
    EON o1 o2 o3   -> EON  (patchOp o1) (patchOp o2) (patchOp o3)
    EOR o1 o2 o3   -> EOR  (patchOp o1) (patchOp o2) (patchOp o3)
    LSL o1 o2 o3   -> LSL  (patchOp o1) (patchOp o2) (patchOp o3)
    LSR o1 o2 o3   -> LSR  (patchOp o1) (patchOp o2) (patchOp o3)
    MOV o1 o2      -> MOV  (patchOp o1) (patchOp o2)
    MOVK o1 o2     -> MOVK (patchOp o1) (patchOp o2)
    MVN o1 o2      -> MVN  (patchOp o1) (patchOp o2)
    ORR o1 o2 o3   -> ORR  (patchOp o1) (patchOp o2) (patchOp o3)
    ROR o1 o2 o3   -> ROR  (patchOp o1) (patchOp o2) (patchOp o3)
    TST o1 o2      -> TST  (patchOp o1) (patchOp o2)

    -- 4. Branch Instructions --------------------------------------------------
    J t            -> J (patchTarget t)
    B t            -> B (patchTarget t)
    BL t           -> BL (patchTarget t)
    BCOND c t      -> BCOND c (patchTarget t)

    -- 5. Atomic Instructions --------------------------------------------------
    -- 6. Conditional Instructions ---------------------------------------------
    CSET o c       -> CSET (patchOp o) c
    CBZ o l        -> CBZ (patchOp o) l
    CBNZ o l       -> CBNZ (patchOp o) l
    -- 7. Load and Store Instructions ------------------------------------------
    STR f o1 o2    -> STR f (patchOp o1) (patchOp o2)
    LDR f o1 o2    -> LDR f (patchOp o1) (patchOp o2)
    STP f o1 o2 o3 -> STP f (patchOp o1) (patchOp o2) (patchOp o3)
    LDP f o1 o2 o3 -> LDP f (patchOp o1) (patchOp o2) (patchOp o3)

    -- 8. Synchronization Instructions -----------------------------------------
    DMBSY          -> DMBSY

    -- 9. Floating Point Instructions ------------------------------------------
    FCVT o1 o2     -> FCVT (patchOp o1) (patchOp o2)
    SCVTF o1 o2    -> SCVTF (patchOp o1) (patchOp o2)
    FCVTZS o1 o2   -> FCVTZS (patchOp o1) (patchOp o2)

    where
        patchOp :: Operand -> Operand
        patchOp (OpReg w r) = OpReg w (env r)
        patchOp (OpRegExt w r x s) = OpRegExt w (env r) x s
        patchOp (OpRegShift w r m s) = OpRegShift w (env r) m s
        patchOp (OpAddr a) = OpAddr (patchAddr a)
        patchOp op = op
        patchTarget :: Target -> Target
        patchTarget (TReg r) = TReg (env r)
        patchTarget t = t
        patchAddr :: AddrMode -> AddrMode
        patchAddr (AddrRegReg r1 r2) = AddrRegReg (env r1) (env r2)
        patchAddr (AddrRegImm r1 i)  = AddrRegImm (env r1) i
        patchAddr (AddrReg r) = AddrReg (env r)
--------------------------------------------------------------------------------
-- | Checks whether this instruction is a jump/branch instruction.
-- One that can change the flow of control in a way that the
-- register allocator needs to worry about.
aarch64_isJumpishInstr :: Instr -> Bool
aarch64_isJumpishInstr instr = case instr of
    ANN _ i -> aarch64_isJumpishInstr i
    CBZ{} -> True
    CBNZ{} -> True
    J{} -> True
    B{} -> True
    BL{} -> True
    BCOND{} -> True
    _ -> False

-- | Checks whether this instruction is a jump/branch instruction.
-- One that can change the flow of control in a way that the
-- register allocator needs to worry about.
aarch64_jumpDestsOfInstr :: Instr -> [BlockId]
aarch64_jumpDestsOfInstr (ANN _ i) = aarch64_jumpDestsOfInstr i
aarch64_jumpDestsOfInstr (CBZ _ t) = [ id | TBlock id <- [t]]
aarch64_jumpDestsOfInstr (CBNZ _ t) = [ id | TBlock id <- [t]]
aarch64_jumpDestsOfInstr (J t) = [id | TBlock id <- [t]]
aarch64_jumpDestsOfInstr (B t) = [id | TBlock id <- [t]]
aarch64_jumpDestsOfInstr (BL t) = [ id | TBlock id <- [t]]
aarch64_jumpDestsOfInstr (BCOND _ t) = [ id | TBlock id <- [t]]
aarch64_jumpDestsOfInstr _ = []

-- | Change the destination of this jump instruction.
-- Used in the linear allocator when adding fixup blocks for join
-- points.
aarch64_patchJumpInstr :: Instr -> (BlockId -> BlockId) -> Instr
aarch64_patchJumpInstr instr patchF
    = case instr of
        ANN d i -> ANN d (aarch64_patchJumpInstr i patchF)
        CBZ r (TBlock bid) -> CBZ r (TBlock (patchF bid))
        CBNZ r (TBlock bid) -> CBNZ r (TBlock (patchF bid))
        J (TBlock bid) -> J (TBlock (patchF bid))
        B (TBlock bid) -> B (TBlock (patchF bid))
        BL (TBlock bid) -> BL (TBlock (patchF bid))
        BCOND c (TBlock bid) -> BCOND c (TBlock (patchF bid))
        _ -> pprPanic "patchJumpInstr" (text $ show instr)

-- -----------------------------------------------------------------------------

-- | An instruction to spill a register into a spill slot.
aarch64_mkSpillInstr
   :: NCGConfig
   -> Reg       -- register to spill
   -> Int       -- current stack delta
   -> Int       -- spill slot to use
   -> Instr
-- XXX this is stupid. We essentially do sp <- sp - 4095; str xN, [sp - ...] ; sp <- sp + 4095
{-
aarch64_mkSpillInstr config reg delta slot | (spillSlotToOffset config slot) - delta > 4095
    = let (!d, !isns) = traceShow msg $ aarch64_mkSpillInstr config reg (delta + delta') slot
      in traceShow "Spill(1) ret" (d, subIsn : isns ++ [addIsn])
      where delta' = 4095
            !addIsn = ADD sp sp (OpImm (ImmInt delta'))
            !subIsn = SUB sp sp (OpImm (ImmInt delta'))
            msg = "Spill(1): " ++ show (spillSlotToOffset config slot) ++ "; Delta: " ++ show delta ++ " -> " ++ show (delta + delta')

aarch64_mkSpillInstr config reg delta slot | (spillSlotToOffset config slot) - delta > 255
    = let (!d, !isns) = traceShow msg $ aarch64_mkSpillInstr config reg (delta + delta') slot
      in traceShow "Spill(2) ret" (d, subIsn : isns ++ [addIsn])
      where delta' = (spillSlotToOffset config slot) - delta
            !addIsn = ADD sp sp (OpImm (ImmInt delta'))
            !subIsn = SUB sp sp (OpImm (ImmInt delta'))
            msg = "Spill(2): " ++ show (spillSlotToOffset config slot) ++ "; Delta: " ++ show delta ++ " -> " ++ show (delta + delta')

aarch64_mkSpillInstr config reg delta slot | (spillSlotToOffset config slot) - delta < -4095
    = let (!d, !isns) = traceShow msg $ aarch64_mkSpillInstr config reg (delta - delta') slot
      in traceShow "Spill(3) ret" (d, addIsn : isns ++ [subIsn])
      where delta' = 4095
            !addIsn = ADD sp sp (OpImm (ImmInt delta'))
            !subIsn = SUB sp sp (OpImm (ImmInt delta'))
            msg = "Spill(3): " ++ show (spillSlotToOffset config slot) ++ "; Delta: " ++ show delta ++ " -> " ++ show (delta + delta')

aarch64_mkSpillInstr config reg delta slot | (spillSlotToOffset config slot) - delta < -256
    = let (!d, !isns) = traceShow msg $ aarch64_mkSpillInstr config reg (delta + delta') slot
      in traceShow "Spill(4) ret" (d, subIsn : isns ++ [addIsn])
      where delta' = (spillSlotToOffset config slot) - delta
            !addIsn = ADD sp sp (OpImm (ImmInt delta'))
            !subIsn = SUB sp sp (OpImm (ImmInt delta'))
            msg = "Spill(4): " ++ show (spillSlotToOffset config slot) ++ "; Delta: " ++ show delta ++ " -> " ++ show (delta + delta')
-}
aarch64_mkSpillInstr config reg delta slot
    = --[
      -- ANN (text "Spill") $
      -- traceShow ("Spill: " ++ show (off - delta)) $
      STR fmt (OpReg W64 reg) (OpAddr (AddrRegImm (regSingle 31) (ImmInt $ off - delta)))
      --]
    where
        fmt = case reg of
            RegReal (RealRegSingle n) | n < 32 -> II64
            _                                  -> FF64
        off = spillSlotToOffset config slot

aarch64_mkLoadInstr
   :: NCGConfig
   -> Reg       -- register to load
   -> Int       -- current stack delta
   -> Int       -- spill slot to use
   -> Instr
-- XXX this is stupid. We essentially do sp <- sp - 4095; str xN, [sp - ...] ; sp <- sp + 4095
{-
aarch64_mkLoadInstr config reg delta slot | (spillSlotToOffset config slot) - delta > 4095
    = let (!d, !isns) =  traceShow msg $ aarch64_mkLoadInstr config reg (delta + delta') slot
      in traceShow "Reload(1) ret" (d, SUB sp sp (OpImm (ImmInt 4095)) : isns ++ [ADD sp sp (OpImm (ImmInt 4095))])
      where delta' = 4095
            msg = "Reload(1): " ++ show (spillSlotToOffset config slot) ++ "; Delta: " ++ show delta ++ " -> " ++ show (delta + delta')

aarch64_mkLoadInstr config reg delta slot | (spillSlotToOffset config slot) - delta > 255
    = let (!d, !isns) = traceShow msg $ aarch64_mkLoadInstr config reg (delta + delta') slot
      in traceShow "Reload(2) ret" (d, SUB sp sp (OpImm (ImmInt delta')) : isns ++ [ADD sp sp (OpImm (ImmInt delta'))])
      where delta' = (spillSlotToOffset config slot) - delta
            msg = "Reload(2): " ++ show (spillSlotToOffset config slot) ++ "; Delta: " ++ show delta ++ " -> " ++ show (delta + delta')

aarch64_mkLoadInstr config reg delta slot | (spillSlotToOffset config slot) - delta < -4095
    = let (!d, !isns) =  traceShow msg $ aarch64_mkLoadInstr config reg (delta + delta') slot
      in traceShow "Reload(3) ret" (d, ADD sp sp (OpImm (ImmInt 4095)) : isns ++ [SUB sp sp (OpImm (ImmInt 4095))])
      where delta' = -4095
            msg = "Reload(3): " ++ show (spillSlotToOffset config slot) ++ "; Delta: " ++ show delta ++ " -> " ++ show (delta + delta')

aarch64_mkLoadInstr config reg delta slot | (spillSlotToOffset config slot) - delta < -256
    = let (!d, !isns) = traceShow msg $ aarch64_mkLoadInstr config reg (delta + delta') slot
      in traceShow "Reload(4) ret" (d, SUB sp sp (OpImm (ImmInt delta')) : isns ++ [ADD sp sp (OpImm (ImmInt delta'))])
      where delta' = (spillSlotToOffset config slot) - delta
            msg = "Reload(4): " ++ show (spillSlotToOffset config slot) ++ "; Delta: " ++ show delta ++ " -> " ++ show (delta + delta')

-}
aarch64_mkLoadInstr config reg delta slot
    = --[
      -- ANN (text "Reload") $
      -- traceShow ("Reload: " ++ show (off - delta)) $
      LDR fmt (OpReg W64 reg) (OpAddr (AddrRegImm (regSingle 31) (ImmInt $ off - delta)))
      -- ]
    where
        fmt = case reg of
            RegReal (RealRegSingle n) | n < 32 -> II64
            _                                  -> FF64
        off = spillSlotToOffset config slot

--------------------------------------------------------------------------------
-- | See if this instruction is telling us the current C stack delta
aarch64_takeDeltaInstr :: Instr -> Maybe Int
aarch64_takeDeltaInstr (ANN _ i) = aarch64_takeDeltaInstr i
aarch64_takeDeltaInstr (DELTA i) = Just i
aarch64_takeDeltaInstr _         = Nothing

-- Not real instructions.  Just meta data
aarch64_isMetaInstr :: Instr -> Bool
aarch64_isMetaInstr instr
 = case instr of
    ANN _ i     -> aarch64_isMetaInstr i
    COMMENT{}   -> True
    MULTILINE_COMMENT{} -> True
    LOCATION{}  -> True
    LDATA{}     -> True
    NEWBLOCK{}  -> True
    DELTA{}     -> True
    PUSH_STACK_FRAME -> True
    POP_STACK_FRAME -> True
    _           -> False

-- | Copy the value in a register to another one.
-- Must work for all register classes.
aarch64_mkRegRegMoveInstr :: Reg -> Reg -> Instr
aarch64_mkRegRegMoveInstr src dst = MOV (OpReg W64 dst) (OpReg W64 src)

-- | Take the source and destination from this reg -> reg move instruction
-- or Nothing if it's not one
aarch64_takeRegRegMoveInstr :: Instr -> Maybe (Reg,Reg)
-- XXX: *if* we enable this here, we run into the elimination shortcut in
--      Linear.hs:441, which does not ensure that the register is free'd
--      before it's reused.  This seesm to be an issue if we have two function
--      calls in the same block.
--
--      y = f a b
--
--      will generate:
--      mov x0 a
--      mov x1 b
--      bl f
--      mov y x0
--
--      We'll elimitate the last mov y x0 call, and alias x0 = y.
--
--      No we'll need to reuse x0 for the next function, and when we
--      try to allocate it, it's already allocated.
--
--aarch64_takeRegRegMoveInstr (MOV (OpReg dst) (OpReg src)) = Just (src, dst)
aarch64_takeRegRegMoveInstr _ = Nothing

-- | Make an unconditional jump instruction.
aarch64_mkJumpInstr :: BlockId -> [Instr]
aarch64_mkJumpInstr id = [B (TBlock id)]

aarch64_mkStackAllocInstr :: Platform -> Int -> [Instr]
aarch64_mkStackAllocInstr platform n
    | n == 0 = []
    | n > 0 && n < 4096 = [ SUB sp sp (OpImm (ImmInt n)) ]
    | n > 0 = SUB sp sp (OpImm (ImmInt 4095)) : aarch64_mkStackAllocInstr platform (n - 4095)
aarch64_mkStackAllocInstr platform n = pprPanic "aarch64_mkStackAllocInstr" (int n)

aarch64_mkStackDeallocInstr :: Platform -> Int -> [Instr]
aarch64_mkStackDeallocInstr platform n
    | n == 0 = []
    | n > 0 && n < 4096 = [ ADD sp sp (OpImm (ImmInt n)) ]
    | n > 0 = ADD sp sp (OpImm (ImmInt 4095)) : aarch64_mkStackDeallocInstr platform (n + 4095)
aarch64_mkStackDeallocInstr platform n = pprPanic "aarch64_mkStackDeallocInstr" (int n)

--
-- See note [extra spill slots] in X86/Instr.hs
--
allocMoreStack
  :: Platform
  -> Int
  -> NatCmmDecl statics GHC.CmmToAsm.AArch64.Instr.Instr
  -> UniqSM (NatCmmDecl statics GHC.CmmToAsm.AArch64.Instr.Instr, [(BlockId,BlockId)])

allocMoreStack _ _ top@(CmmData _ _) = return (top,[])
allocMoreStack platform slots proc@(CmmProc info lbl live (ListGraph code)) = do
    let entries = entryBlocks proc

    uniqs <- replicateM (length entries) getUniqueM

    let
      delta = ((x + stackAlign - 1) `quot` stackAlign) * stackAlign -- round up
        where x = slots * spillSlotSize -- sp delta

      alloc   = mkStackAllocInstr   platform delta
      dealloc = mkStackDeallocInstr platform delta

      retargetList = (zip entries (map mkBlockId uniqs))

      new_blockmap :: LabelMap BlockId
      new_blockmap = mapFromList retargetList

      insert_stack_insn (BasicBlock id insns)
        | Just new_blockid <- mapLookup id new_blockmap
        = [ BasicBlock id $ alloc ++ [ B (TBlock new_blockid) ]
          , BasicBlock new_blockid block' ]
        | otherwise
        = [ BasicBlock id block' ]
        where
          block' = foldr insert_dealloc [] insns

      insert_dealloc insn r = case insn of
        J _ -> dealloc ++ (insn : r)
        _other | aarch64_jumpDestsOfInstr insn /= []
            -> aarch64_patchJumpInstr insn retarget : r
        _other -> insn : r

        where retarget b = fromMaybe b (mapLookup b new_blockmap)

      new_code = concatMap insert_stack_insn code
    -- in
    return (CmmProc info lbl live (ListGraph new_code), retargetList)
-- -----------------------------------------------------------------------------
-- Machine's assembly language

-- We have a few common "instructions" (nearly all the pseudo-ops) but
-- mostly all of 'Instr' is machine-specific.

data Instr
    -- comment pseudo-op
    = COMMENT SDoc
    | MULTILINE_COMMENT SDoc

    -- Annotated instruction. Should print <instr> # <doc>
    | ANN SDoc Instr

    -- location pseudo-op (file, line, col, name)
    | LOCATION Int Int Int String

    -- some static data spat out during code
    -- generation.  Will be extracted before
    -- pretty-printing.
    | LDATA   Section RawCmmStatics

    -- start a new basic block.  Useful during
    -- codegen, removed later.  Preceding
    -- instruction should be a jump, as per the
    -- invariants for a BasicBlock (see Cmm).
    | NEWBLOCK BlockId

    -- specify current stack offset for
    -- benefit of subsequent passes
    | DELTA   Int

    -- 0. Pseudo Instructions --------------------------------------------------
    -- These are instructions not contained or only partially contained in the
    -- official ISA, but make reading clearer. Some of them might even be
    -- implemented in the assembler, but are not guaranteed to be portable.
    -- | SXTB Operand Operand
    -- | SXTH Operand Operand
    -- | SXTW Operand Operand
    -- | SXTX Operand Operand
    | PUSH_STACK_FRAME
    | POP_STACK_FRAME
    -- 1. Arithmetic Instructions ----------------------------------------------
    -- | ADC Operand Operand Operang -- rd = rn + rm + C
    -- | ADCS ...
    | ADD Operand Operand Operand -- rd = rn + rm
    | ADDS Operand Operand Operand -- rd = rn + rm
    -- | ADR ...
    -- | ADRP ...
    | CMN Operand Operand -- rd + op2
    | CMP Operand Operand -- rd − op2
    -- | MADD ...
    -- | MNEG ...
    | MSUB Operand Operand Operand Operand -- rd = ra − rn × rm
    | MUL Operand Operand Operand -- rd = rn × rm
    | NEG Operand Operand -- rd = −op2
    -- | NEGS ...
    -- | NGC ...
    -- | NGCS ...
    -- | SBC ...
    -- | SBCS ...
    | SDIV Operand Operand Operand -- rd = rn ÷ rm
    -- | SMADDL ...
    -- | SMNEGL ...
    -- | SMSUBL ...
    -- | SMULH ...
    -- | SMULL ...
    | SUB Operand Operand Operand -- rd = rn - op2
    -- | SUBS ...
    | UDIV Operand Operand Operand -- rd = rn ÷ rm
    -- | UMADDL ...  -- Xd = Xa + Wn × Wm
    -- | UMNEGL ... -- Xd = − Wn × Wm
    -- | UMSUBL ... -- Xd = Xa − Wn × Wm
    -- | UMULH ... -- Xd = (Xn × Xm)_127:64
    -- | UMULL ... -- Xd = Wn × Wm

    -- 2. Bit Manipulation Instructions ----------------------------------------
    | SBFM Operand Operand Operand Operand -- rd = rn[i,j]
    -- SXTB = SBFM <Wd>, <Wn>, #0, #7
    -- SXTH = SBFM <Wd>, <Wn>, #0, #15
    -- SXTW = SBFM <Wd>, <Wn>, #0, #31
    | UBFM Operand Operand Operand Operand -- rd = rn[i,j]
    -- UXTB = UBFM <Wd>, <Wn>, #0, #7
    -- UXTH = UBFM <Wd>, <Wn>, #0, #15

    -- XXX
    -- 3. Logical and Move Instructions ----------------------------------------
    | AND Operand Operand Operand -- rd = rn & op2
    | ANDS Operand Operand Operand -- rd = rn & op2
    | ASR Operand Operand Operand -- rd = rn ≫ rm  or  rd = rn ≫ #i, i is 6 bits
    | BIC Operand Operand Operand -- rd = rn & ∼op2
    | BICS Operand Operand Operand -- rd = rn & ∼op2
    | EON Operand Operand Operand -- rd = rn ⊕ ∼op2
    | EOR Operand Operand Operand -- rd = rn ⊕ op2
    | LSL Operand Operand Operand -- rd = rn ≪ rm  or rd = rn ≪ #i, i is 6 bits
    | LSR Operand Operand Operand -- rd = rn ≫ rm  or rd = rn ≫ #i, i is 6 bits
    | MOV Operand Operand -- rd = rn  or  rd = #i
    | MOVK Operand Operand
    -- | MOVN Operand Operand
    -- | MOVZ Operand Operand
    | MVN Operand Operand -- rd = ~rn
    | ORN Operand Operand Operand -- rd = rn | ∼op2
    | ORR Operand Operand Operand -- rd = rn | op2
    | ROR Operand Operand Operand -- rd = rn ≫ rm  or  rd = rn ≫ #i, i is 6 bits
    | TST Operand Operand -- rn & op2
    -- Load and stores.
    -- XXX STR/LDR might want to change to STP/LDP with XZR for the second register.
    | STR Format Operand Operand -- str Xn, address-mode // Xn -> *addr
    | LDR Format Operand Operand -- ldr Xn, address-mode // Xn <- *addr
    | STP Format Operand Operand Operand -- stp Xn, Xm, address-mode // Xn -> *addr, Xm -> *(addr + 8)
    | LDP Format Operand Operand Operand -- stp Xn, Xm, address-mode // Xn <- *addr, Xm <- *(addr + 8)

    -- Conditional instructions
    | CSET Operand Cond   -- if(cond) op <- 1 else op <- 0

    | CBZ Operand Target  -- if op == 0, then branch.
    | CBNZ Operand Target -- if op /= 0, then branch.
    -- Branching.
    | J Target            -- like B, but only generated from genJump. Used to distinguish genJumps from others.
    | B Target            -- unconditional branching b/br. (To a blockid, label or register)
    | BL Target           -- branch and link (e.g. set x30 to next pc, and branch)
    | BCOND Cond Target   -- branch with condition. b.<cond>

    -- 8. Synchronization Instructions -----------------------------------------
    | DMBSY
    -- 9. Floating Point Instructions
    -- Float ConVerT
    | FCVT Operand Operand
    -- Signed ConVerT Float
    | SCVTF Operand Operand
    -- Float ConVerT to Zero Signed
    | FCVTZS Operand Operand

instance Show Instr where
    show (LDR f o1 o2) = "LDR " ++ show o1 ++ ", " ++ show o2
    show (MOV o1 o2) = "MOV " ++ show o1 ++ ", " ++ show o2
    show _ = "missing"

data Target
    = TBlock BlockId
    | TLabel CLabel
    | TReg   Reg


-- Extension
-- {Unsigned|Signed}XT{Byte|Half|Word|Doube}
data ExtMode
    = EUXTB | EUXTH | EUXTW | EUXTX
    | ESXTB | ESXTH | ESXTW | ESXTX
    deriving (Eq, Show)

data ShiftMode
    = SLSL | SLSR | SASR | SROR
    deriving (Eq, Show)


-- We can also add ExtShift to Extension.
-- However at most 3bits.
type ExtShift = Int
-- at most 6bits
type RegShift = Int

data Operand
        = OpReg Width Reg            -- register
        | OpRegExt Width Reg ExtMode ExtShift -- rm, <ext>[, <shift left>]
        | OpRegShift Width Reg ShiftMode RegShift     -- rm, <shift>, <0-64>
        | OpImm Imm            -- immediate value
        | OpImmShift Imm ShiftMode RegShift
        | OpAddr AddrMode       -- memory reference
        deriving (Eq, Show)

-- Smart constructors
opReg :: Width -> Reg -> Operand
opReg = OpReg

xzr, wzr, sp :: Operand
xzr = OpReg W64 (RegReal (RealRegSingle (-1)))
wzr = OpReg W32 (RegReal (RealRegSingle (-1)))
sp  = OpReg W64 (RegReal (RealRegSingle 31))

_x :: Int -> Operand
_x i = OpReg W64 (RegReal (RealRegSingle i))
x0,  x1,  x2,  x3,  x4,  x5,  x6,  x7  :: Operand
x8,  x9,  x10, x11, x12, x13, x14, x15 :: Operand
x16, x17, x18, x19, x20, x21, x22, x23 :: Operand
x24, x25, x26, x27, x28, x29, x30, x31 :: Operand
x0  = OpReg W64 (RegReal (RealRegSingle  0))
x1  = OpReg W64 (RegReal (RealRegSingle  1))
x2  = OpReg W64 (RegReal (RealRegSingle  2))
x3  = OpReg W64 (RegReal (RealRegSingle  3))
x4  = OpReg W64 (RegReal (RealRegSingle  4))
x5  = OpReg W64 (RegReal (RealRegSingle  5))
x6  = OpReg W64 (RegReal (RealRegSingle  6))
x7  = OpReg W64 (RegReal (RealRegSingle  7))
x8  = OpReg W64 (RegReal (RealRegSingle  8))
x9  = OpReg W64 (RegReal (RealRegSingle  9))
x10 = OpReg W64 (RegReal (RealRegSingle 10))
x11 = OpReg W64 (RegReal (RealRegSingle 11))
x12 = OpReg W64 (RegReal (RealRegSingle 12))
x13 = OpReg W64 (RegReal (RealRegSingle 13))
x14 = OpReg W64 (RegReal (RealRegSingle 14))
x15 = OpReg W64 (RegReal (RealRegSingle 15))
x16 = OpReg W64 (RegReal (RealRegSingle 16))
x17 = OpReg W64 (RegReal (RealRegSingle 17))
x18 = OpReg W64 (RegReal (RealRegSingle 18))
x19 = OpReg W64 (RegReal (RealRegSingle 19))
x20 = OpReg W64 (RegReal (RealRegSingle 20))
x21 = OpReg W64 (RegReal (RealRegSingle 21))
x22 = OpReg W64 (RegReal (RealRegSingle 22))
x23 = OpReg W64 (RegReal (RealRegSingle 23))
x24 = OpReg W64 (RegReal (RealRegSingle 24))
x25 = OpReg W64 (RegReal (RealRegSingle 25))
x26 = OpReg W64 (RegReal (RealRegSingle 26))
x27 = OpReg W64 (RegReal (RealRegSingle 27))
x28 = OpReg W64 (RegReal (RealRegSingle 28))
x29 = OpReg W64 (RegReal (RealRegSingle 29))
x30 = OpReg W64 (RegReal (RealRegSingle 30))
x31 = OpReg W64 (RegReal (RealRegSingle 31))

_d :: Int -> Operand
_d = OpReg W64 . RegReal . RealRegSingle
d0,  d1,  d2,  d3,  d4,  d5,  d6,  d7  :: Operand
d8,  d9,  d10, d11, d12, d13, d14, d15 :: Operand
d16, d17, d18, d19, d20, d21, d22, d23 :: Operand
d24, d25, d26, d27, d28, d29, d30, d31 :: Operand
d0  = OpReg W64 (RegReal (RealRegSingle 32))
d1  = OpReg W64 (RegReal (RealRegSingle 33))
d2  = OpReg W64 (RegReal (RealRegSingle 34))
d3  = OpReg W64 (RegReal (RealRegSingle 35))
d4  = OpReg W64 (RegReal (RealRegSingle 36))
d5  = OpReg W64 (RegReal (RealRegSingle 37))
d6  = OpReg W64 (RegReal (RealRegSingle 38))
d7  = OpReg W64 (RegReal (RealRegSingle 39))
d8  = OpReg W64 (RegReal (RealRegSingle 40))
d9  = OpReg W64 (RegReal (RealRegSingle 41))
d10 = OpReg W64 (RegReal (RealRegSingle 42))
d11 = OpReg W64 (RegReal (RealRegSingle 43))
d12 = OpReg W64 (RegReal (RealRegSingle 44))
d13 = OpReg W64 (RegReal (RealRegSingle 45))
d14 = OpReg W64 (RegReal (RealRegSingle 46))
d15 = OpReg W64 (RegReal (RealRegSingle 47))
d16 = OpReg W64 (RegReal (RealRegSingle 48))
d17 = OpReg W64 (RegReal (RealRegSingle 49))
d18 = OpReg W64 (RegReal (RealRegSingle 50))
d19 = OpReg W64 (RegReal (RealRegSingle 51))
d20 = OpReg W64 (RegReal (RealRegSingle 52))
d21 = OpReg W64 (RegReal (RealRegSingle 53))
d22 = OpReg W64 (RegReal (RealRegSingle 54))
d23 = OpReg W64 (RegReal (RealRegSingle 55))
d24 = OpReg W64 (RegReal (RealRegSingle 56))
d25 = OpReg W64 (RegReal (RealRegSingle 57))
d26 = OpReg W64 (RegReal (RealRegSingle 58))
d27 = OpReg W64 (RegReal (RealRegSingle 59))
d28 = OpReg W64 (RegReal (RealRegSingle 60))
d29 = OpReg W64 (RegReal (RealRegSingle 61))
d30 = OpReg W64 (RegReal (RealRegSingle 62))
d31 = OpReg W64 (RegReal (RealRegSingle 63))

opRegUExt :: Width -> Reg -> Operand
opRegUExt W64 r = OpRegExt W64 r EUXTX 0
opRegUExt W32 r = OpRegExt W32 r EUXTW 0
opRegUExt W16 r = OpRegExt W16 r EUXTH 0
opRegUExt W8  r = OpRegExt W8  r EUXTB 0

opRegSExt :: Width -> Reg -> Operand
opRegSExt W64 r = OpRegExt W64 r ESXTX 0
opRegSExt W32 r = OpRegExt W32 r ESXTW 0
opRegSExt W16 r = OpRegExt W16 r ESXTH 0
opRegSExt W8  r = OpRegExt W8  r ESXTB 0