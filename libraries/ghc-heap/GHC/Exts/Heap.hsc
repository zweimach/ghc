{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GHCForeignImportPrim #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|
Module      :  GHC.Exts.Heap
Copyright   :  (c) 2012 Joachim Breitner
License     :  BSD3
Maintainer  :  Joachim Breitner <mail@joachim-breitner.de>

With this module, you can investigate the heap representation of Haskell
values, i.e. to investigate sharing and lazy evaluation.
-}


module GHC.Exts.Heap (
    -- * Heap data types
    GenClosure(..),
    Closure,
    allPtrs,
    ClosureType(..),
    StgInfoTable(..),
    HalfWord,
    -- * Reading from the heap
    getClosureData,
    getBoxedClosureData,
    getClosureRaw,

    -- * Boxes
    Box(..),
    asBox,
    areBoxesEqual,
    )
    where

import GHC.Exts         ( Any, Ptr(..), Addr#, Int(..), Word(..), Word#, Int#
                        , ByteArray#, Array#
                        , sizeofByteArray#, sizeofArray#, indexArray#
                        , indexWordArray#, unsafeCoerce# )

import GHC.Arr          (Array (..))


import Foreign          hiding ( void )
import Numeric          ( showHex )
import Data.Char
import Data.List
import Data.Functor
import Data.Foldable    ( Foldable )
import Data.Traversable ( Traversable )
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Control.Exception.Base (evaluate)

#include "ghcautoconf.h"

-- | An arbitrary Haskell value in a safe Box. The point is that even
-- unevaluated thunks can safely be moved around inside the Box, and when
-- required, e.g. in 'getBoxedClosureData', the function knows how far it has
-- to evaluate the argument.
data Box = Box Any

#if SIZEOF_VOID_P == 8
type HalfWord = Word32
#else
type HalfWord = Word16
#endif

instance Show Box where
-- From libraries/base/GHC/Ptr.lhs
   showsPrec _ (Box a) rs =
    -- unsafePerformIO (print "↓" >> pClosure a) `seq`
    pad_out (showHex addr "") ++ (if tag>0 then "/" ++ show tag else "") ++ rs
     where
       ptr  = W# (aToWord# a)
       tag  = ptr .&. fromIntegral tAG_MASK -- ((1 `shiftL` TAG_BITS) -1)
       addr = ptr - tag
        -- want 0s prefixed to pad it out to a fixed length.
       pad_out ls =
          '0':'x':(replicate (2*wORD_SIZE - length ls) '0') ++ ls

-- | Boxes can be compared, but this is not pure, as different heap objects can,
-- after garbage collection, become the same object.
areBoxesEqual :: Box -> Box -> IO Bool
areBoxesEqual (Box a) (Box b) = case reallyUnsafePtrEqualityUpToTag# a b of
    0# -> pure False
    _  -> pure True


{-|
  This takes an arbitrary value and puts it into a box. Note that calls like

  > asBox (head list)

  will put the thunk \"head list\" into the box, /not/ the element at the head
  of the list. For that, use careful case expressions:

  > case list of x:_ -> asBox x
-}
asBox :: a -> Box
asBox x = Box (unsafeCoerce# x)

{-
   StgInfoTable parsing derived from ByteCodeItbls.lhs
   Removed the code parameter for now
   Replaced Type by an enumeration
   Remove stuff dependent on GHCI_TABLES_NEXT_TO_CODE
 -}

-- | This is a somewhat faithful representation of an info table. See
-- <http://hackage.haskell.org/trac/ghc/browser/includes/rts/storage/InfoTables.h>
-- for more details on this data structure. Note that the 'Storable' instance
-- provided here does _not_ support writing.
data StgInfoTable = StgInfoTable {
   ptrs   :: !HalfWord,
   nptrs  :: !HalfWord,
   cltype :: !ClosureType,
   srtlen :: !HalfWord
  }
  deriving (Show)

peekItbl :: Ptr StgInfoTable -> IO StgInfoTable
peekItbl a0 = do
#if defined(TABLES_NEXT_TO_CODE)
  let entry' = Nothing
#else
  entry' <- Just <$> (#peek StgInfoTable, entry) a0
#endif
  ptrs' <- (#peek StgInfoTable, layout.payload.ptrs) a0
  nptrs' <- (#peek StgInfoTable, layout.payload.nptrs) a0
  tipe' <- (#peek StgInfoTable, type) a0
  srtlen' <- (#peek StgInfoTable, srt_bitmap) a0
  return StgInfoTable
    { entry  = entry'
    , ptrs   = ptrs'
    , nptrs  = nptrs'
    , cltype = tipe'
    , srtlen = srtlen'
    }

fieldSz :: Storable b => (a -> b) -> a -> Int
fieldSz sel x = sizeOf (sel x)

load :: Storable a => PtrIO a
load = do addr <- advance
          lift (peek addr)

type PtrIO = StateT (Ptr Word8) IO

advance :: Storable a => PtrIO (Ptr a)
advance = StateT adv where
    adv addr = case castPtr addr of { addrCast -> return
        (addrCast, addr `plusPtr` sizeOfPointee addrCast) }

sizeOfPointee :: forall a. (Storable a) => Ptr a -> Int
sizeOfPointee addr = sizeOf (undefined :: a)

{-
   Data Type representing Closures
 -}


-- | A closure type enumeration, in order matching the actual value on the heap.
-- Needs to be synchronized with
-- <http://hackage.haskell.org/trac/ghc/browser/includes/rts/storage/ClosureTypes.h>
data ClosureType
    = INVALID_OBJECT
    | CONSTR
    | CONSTR_1_0
    | CONSTR_0_1
    | CONSTR_2_0
    | CONSTR_1_1
    | CONSTR_0_2
    | CONSTR_NOCAF
    | FUN
    | FUN_1_0
    | FUN_0_1
    | FUN_2_0
    | FUN_1_1
    | FUN_0_2
    | FUN_STATIC
    | THUNK
    | THUNK_1_0
    | THUNK_0_1
    | THUNK_2_0
    | THUNK_1_1
    | THUNK_0_2
    | THUNK_STATIC
    | THUNK_SELECTOR
    | BCO
    | AP
    | PAP
    | AP_STACK
    | IND
    | IND_STATIC
    | RET_BCO
    | RET_SMALL
    | RET_BIG
    | RET_FUN
    | UPDATE_FRAME
    | CATCH_FRAME
    | UNDERFLOW_FRAME
    | STOP_FRAME
    | BLOCKING_QUEUE
    | BLACKHOLE
    | MVAR_CLEAN
    | MVAR_DIRTY
    | TVAR
    | ARR_WORDS
    | MUT_ARR_PTRS_CLEAN
    | MUT_ARR_PTRS_DIRTY
    | MUT_ARR_PTRS_FROZEN0
    | MUT_ARR_PTRS_FROZEN
    | MUT_VAR_CLEAN
    | MUT_VAR_DIRTY
    | WEAK
    | PRIM
    | MUT_PRIM
    | TSO
    | STACK
    | TREC_CHUNK
    | ATOMICALLY_FRAME
    | CATCH_RETRY_FRAME
    | CATCH_STM_FRAME
    | WHITEHOLE
    | SMALL_MUT_ARR_PTRS_CLEAN
    | SMALL_MUT_ARR_PTRS_DIRTY
    | SMALL_MUT_ARR_PTRS_FROZEN0
    | SMALL_MUT_ARR_PTRS_FROZEN
    | COMPACT_NFDATA
    | N_CLOSURE_TYPES
 deriving (Show, Eq, Enum, Ord)

-- | This is the main data type of this module, representing a Haskell value on
-- the heap. This reflects
-- <http://hackage.haskell.org/trac/ghc/browser/includes/rts/storage/Closures.h>
--
-- The data type is parametrized by the type to store references in, which
-- is usually a 'Box' with appropriate type synonym 'Closure'.
data GenClosure b
  = -- | A constructor
    ConsClosure
        { info       :: !StgInfoTable
        , ptrArgs    :: ![b]
        , dataArgs   :: ![Word]
        , pkg        :: !String
        , modl       :: !String
        , name       :: !String
        }
    -- | A thunk (e.g. unevaluated expression)
  | ThunkClosure
        { info       :: !StgInfoTable
        , ptrArgs    :: ![b]
        , dataArgs   :: ![Word]
        }
    -- | A field selector
  | SelectorClosure
        { info       :: !StgInfoTable
        , selectee   :: !b
        }
    -- | A garbage-collector indirection
  | IndClosure
        { info       :: !StgInfoTable
        , indirectee :: !b
        }
    -- | A blackhole
  | BlackholeClosure
        { info       :: !StgInfoTable
        , indirectee :: !b
        }
    -- In GHCi, if Linker.h would allow a reverse lookup, we could for exported
    -- functions fun actually find the name here.
    -- At least the other direction works via "lookupSymbol
    -- base_GHCziBase_zpzp_closure" and yields the same address (up to tags)
    -- | A function application
  | APClosure
        { info       :: !StgInfoTable
        , arity      :: !HalfWord
        , n_args     :: !HalfWord
        , fun        :: !b
        , payload    :: ![b]
        }
    -- | An unsaturated function application
  | PAPClosure
        { info       :: !StgInfoTable
        , arity      :: !HalfWord
        , n_args     :: !HalfWord
        , fun        :: !b
        , payload    :: ![b]
        }
    -- | An application of a function to a stack of arguments
  | APStackClosure
        { info       :: !StgInfoTable
        , fun        :: !b
        , payload    :: ![b]
        }
    -- | A byte-code object.
  | BCOClosure
        { info       :: !StgInfoTable
        , instrs     :: !b
        , literals   :: !b
        , bcoptrs    :: !b
        , arity      :: !HalfWord
        , size       :: !HalfWord
        , bitmap     :: !Word
        }
    -- | An @ByteArray#@
  | ArrWordsClosure
        { info       :: !StgInfoTable
        , bytes      :: !Word
        , arrWords   :: ![Word]
        }
    -- | An @MutableByteArray#@
  | MutArrClosure
        { info       :: !StgInfoTable
        , mccPtrs    :: !Word
        , mccSize    :: !Word
        , mccPayload :: ![b]
        -- Card table ignored
        }
    -- | An @MutVar#@
  | MutVarClosure
        { info       :: !StgInfoTable
        , var        :: !b
        }
    -- | An @MVar#@
  | MVarClosure
        { info       :: !StgInfoTable
        , queueHead  :: !b
        , queueTail  :: !b
        , value      :: !b
        }
    -- | TODO
  | FunClosure
        { info       :: !StgInfoTable
        , ptrArgs    :: ![b]
        , dataArgs   :: ![Word]
        }
    -- | An STM blocking queue.
  | BlockingQueueClosure
        { info       :: !StgInfoTable
        , link       :: !b
        , blackHole  :: !b
        , owner      :: !b
        , queue      :: !b
        }
    -- | Another kind of closure
  | OtherClosure
        { info       :: !StgInfoTable
        , hvalues    :: ![b]
        , rawWords   :: ![Word]
        }
  | UnsupportedClosure
        { info       :: !StgInfoTable
        }
 deriving (Show, Functor, Foldable, Traversable)


type Closure = GenClosure Box

-- | For generic code, this function returns all referenced closures.
allPtrs :: GenClosure b -> [b]
allPtrs (ConsClosure {..}) = ptrArgs
allPtrs (ThunkClosure {..}) = ptrArgs
allPtrs (SelectorClosure {..}) = [selectee]
allPtrs (IndClosure {..}) = [indirectee]
allPtrs (BlackholeClosure {..}) = [indirectee]
allPtrs (APClosure {..}) = fun:payload
allPtrs (PAPClosure {..}) = fun:payload
allPtrs (APStackClosure {..}) = fun:payload
allPtrs (BCOClosure {..}) = [instrs,literals,bcoptrs]
allPtrs (ArrWordsClosure {..}) = []
allPtrs (MutArrClosure {..}) = mccPayload
allPtrs (MutVarClosure {..}) = [var]
allPtrs (MVarClosure {..}) = [queueHead,queueTail,value]
allPtrs (FunClosure {..}) = ptrArgs
allPtrs (BlockingQueueClosure {..}) = [link, blackHole, owner, queue]
allPtrs (OtherClosure {..}) = hvalues
allPtrs (UnsupportedClosure {..}) = []


foreign import prim "aToWordzh" aToWord# :: Any -> Word#

foreign import prim "slurpClosurezh"
    slurpClosure# :: Any -> (# Addr#, ByteArray#, Array# b #)

foreign import prim "reallyUnsafePtrEqualityUpToTag"
    reallyUnsafePtrEqualityUpToTag# :: Any -> Any -> Int#

--pClosure x = do
--    getClosure x >>= print

-- | This returns the raw representation of the given argument. The second
-- component of the triple are the words on the heap, and the third component
-- are those words that are actually pointers. Once back in Haskell word, the
-- 'Word'  may be outdated after a garbage collector run, but the corresponding
-- 'Box' will still point to the correct value.
getClosureRaw :: a -> IO (Ptr StgInfoTable, [Word], [Box])
getClosureRaw x =
    case slurpClosure# (unsafeCoerce# x) of
        (# iptr, dat, ptrs #) -> do
            let nelems = (I# (sizeofByteArray# dat)) `div` wORD_SIZE
                end = fromIntegral nelems - 1
                rawWords = [W# (indexWordArray# dat i) | I# i <- [0.. end] ]
                pelems = I# (sizeofArray# ptrs)
                ptrList = amap' Box $ Array 0 (pelems - 1) pelems ptrs
            -- This is just for good measure, and seems to be not important.
            mapM_ evaluate ptrList
            -- This seems to be required to avoid crashes as well
            void $ evaluate nelems
            -- The following deep evaluation is crucial to avoid crashes
            -- (but why)?
            mapM_ evaluate rawWords
            pure (Ptr iptr, rawWords, ptrList)

-- From compiler/ghci/RtClosureInspect.hs
amap' :: (t -> b) -> Array Int t -> [b]
amap' f (Array i0 i _ arr#) = map g [0 .. i - i0]
    where g (I# i#) = case indexArray# arr# i# of
                          (# e #) -> f e

-- derived from vacuum-1.0.0.2/src/GHC/Vacuum/Internal.hs, which got it from
-- compiler/ghci/DebuggerUtils.hs
dataConInfoPtrToNames :: Ptr StgInfoTable -> IO (String, String, String)
dataConInfoPtrToNames ptr = do
    conDescAddress <- getConDescAddress ptr
    wl <- peekArray0 0 conDescAddress
    let (pkg, modl, name) = parse wl
    pure (b2s pkg, b2s modl, b2s name)
  where
    b2s :: [Word8] -> String
    b2s = fmap (chr . fromIntegral)

    getConDescAddress :: Ptr StgInfoTable -> IO (Ptr Word8)
    getConDescAddress ptr'
      | True = do
          offsetToString <- peek (ptr' `plusPtr` (negate wORD_SIZE))
          pure $ (ptr' `plusPtr` stdInfoTableSizeB)
                    `plusPtr` (fromIntegral (offsetToString :: Word))
    -- This is code for !ghciTablesNextToCode:
    {-
      | otherwise = peek . intPtrToPtr
                      . (+ fromIntegral
                            stdInfoTableSizeB)
                        . ptrToIntPtr $ ptr
    -}

    -- hmmmmmm. Is there any way to tell this?
    opt_SccProfilingOn = False

    stdInfoTableSizeW :: Int
    -- The size of a standard info table varies with profiling/ticky etc,
    -- so we can't get it from Constants
    -- It must vary in sync with mkStdInfoTable
    stdInfoTableSizeW
      = size_fixed + size_prof
      where
        size_fixed = 2  -- layout, type
        size_prof | opt_SccProfilingOn = 2
                  | otherwise    = 0

    stdInfoTableSizeB :: Int
    stdInfoTableSizeB = stdInfoTableSizeW * wORD_SIZE

-- From vacuum-1.0.0.2/src/GHC/Vacuum/Internal.hs
parse :: [Word8] -> ([Word8], [Word8], [Word8])
parse input = if not . all (>0) . fmap length $ [pkg,modl,occ]
                --then (error . concat)
                --        ["getConDescAddress:parse:"
                --        ,"(not . all (>0) . fmap le"
                --        ,"ngth $ [pkg,modl,occ]"]
                -- Not in the pkg.modl.occ format, for example END_TSO_QUEUE
                then ([], [], input)
                else (pkg, modl, occ)
--   = ASSERT(all (>0) (map length [pkg, modl, occ])) (pkg, modl, occ)
  where
        (pkg, rest1) = break (== fromIntegral (ord ':')) input
        (modl, occ)
            = (concat $ intersperse [dot] $ reverse modWords, occWord)
            where
            (modWords, occWord) =
                if (length rest1 < 1) --  XXXXXXXXx YUKX
                    --then error "getConDescAddress:parse:length rest1 < 1"
                    then parseModOcc [] []
                    else parseModOcc [] (tail rest1)
        -- ASSERT(length rest1 > 0) (parseModOcc [] (tail rest1))
        dot = fromIntegral (ord '.')
        parseModOcc :: [[Word8]] -> [Word8] -> ([[Word8]], [Word8])
        parseModOcc acc str
            = case break (== dot) str of
                (top, []) -> (acc, top)
                (top, _:bot) -> parseModOcc (top : acc) bot


-- | This function returns parsed heap representation of the argument _at this
-- moment_, even if it is unevaluated or an indirection or other exotic stuff.
-- Beware when passing something to this function, the same caveats as for
-- 'asBox' apply.
getClosureData :: a -> IO Closure
getClosureData x = do
    (iptr, wds, ptrs) <- getClosureRaw x
    itbl <- peek iptr
    case cltype itbl of
        t | t >= CONSTR && t <= CONSTR_NOCAF -> do
            (pkg, modl, name) <- dataConInfoPtrToNames iptr
            if modl == "ByteCodeInstr" && name == "BreakInfo"
              then pure $ UnsupportedClosure itbl
              else
                let count = length ptrs + 1 in
                pure $ ConsClosure itbl ptrs (drop count wds) pkg modl name

        t | t >= THUNK && t <= THUNK_STATIC -> do
            pure $ ThunkClosure itbl ptrs (drop (length ptrs + 2) wds)

        t | t >= FUN && t <= FUN_STATIC -> do
            pure $ FunClosure itbl ptrs (drop (length ptrs + 1) wds)

        AP -> do
            unless (length ptrs >= 1) $
                fail "Expected at least 1 ptr argument to AP"
            unless (length wds >= 3) $
                fail "Expected at least 3 raw words to AP"
            pure $ APClosure itbl
                (fromIntegral $ wds !! 2)
                (fromIntegral $ shiftR (wds !! 2) (wORD_SIZE_IN_BITS `div` 2))
                (head ptrs) (tail ptrs)

        PAP -> do
            unless (length ptrs >= 1) $
                fail "Expected at least 1 ptr argument to PAP"
            unless (length wds >= 3) $
                fail "Expected at least 3 raw words to AP"
            pure $ PAPClosure itbl
                (fromIntegral $ wds !! 2)
                (fromIntegral $ shiftR (wds !! 2) (wORD_SIZE_IN_BITS `div` 2))
                (head ptrs) (tail ptrs)

        AP_STACK -> do
            unless (length ptrs >= 1) $
                fail "Expected at least 1 ptr argument to AP_STACK"
            pure $ APStackClosure itbl (head ptrs) (tail ptrs)

        THUNK_SELECTOR -> do
            unless (length ptrs >= 1) $
                fail "Expected at least 1 ptr argument to THUNK_SELECTOR"
            pure $ SelectorClosure itbl (head ptrs)

        IND -> do
            unless (length ptrs >= 1) $
                fail "Expected at least 1 ptr argument to IND"
            pure $ IndClosure itbl (head ptrs)
        IND_STATIC -> do
            unless (length ptrs >= 1) $
                fail "Expected at least 1 ptr argument to IND_STATIC"
            pure $ IndClosure itbl (head ptrs)
        BLACKHOLE -> do
            unless (length ptrs >= 1) $
                fail "Expected at least 1 ptr argument to BLACKHOLE"
            pure $ BlackholeClosure itbl (head ptrs)

        BCO -> do
            unless (length ptrs >= 3) $
                fail $ "Expected at least 3 ptr argument to BCO, found "
                        ++ show (length ptrs)
            unless (length wds >= 6) $
                fail $ "Expected at least 6 words to BCO, found "
                        ++ show (length wds)
            pure $ BCOClosure itbl (ptrs !! 0) (ptrs !! 1) (ptrs !! 2)
                (fromIntegral $ wds !! 4)
                (fromIntegral $ shiftR (wds !! 4) (wORD_SIZE_IN_BITS `div` 2))
                (wds !! 5)

        ARR_WORDS -> do
            unless (length wds >= 2) $
                fail $ "Expected at least 2 words to ARR_WORDS, found "
                        ++ show (length wds)
            pure $ ArrWordsClosure itbl (wds !! 1) (drop 2 wds)

        t | t == MUT_ARR_PTRS_FROZEN || t == MUT_ARR_PTRS_FROZEN0 -> do
            unless (length wds >= 3) $
                fail $ "Expected at least 3 words to MUT_ARR_PTRS_FROZEN0 "
                        ++ "found " ++ show (length wds)
            pure $ MutArrClosure itbl (wds !! 1) (wds !! 2) ptrs

        t | t == MUT_VAR_CLEAN || t == MUT_VAR_DIRTY ->
            pure $ MutVarClosure itbl (head ptrs)

        t | t == MVAR_CLEAN || t == MVAR_DIRTY -> do
            unless (length ptrs >= 3) $
                fail $ "Expected at least 3 ptrs to MVAR, found "
                        ++ show (length ptrs)
            pure $ MVarClosure itbl (ptrs !! 0) (ptrs !! 1) (ptrs !! 2)

        BLOCKING_QUEUE ->
            pure $ OtherClosure itbl ptrs wds
        --    pure $ BlockingQueueClosure itbl
        --        (ptrs !! 0) (ptrs !! 1) (ptrs !! 2) (ptrs !! 3)

        --  pure $ OtherClosure itbl ptrs wds
        --
        _ ->
            pure $ UnsupportedClosure itbl

-- | Like 'getClosureData', but taking a 'Box', so it is easier to work with.
getBoxedClosureData :: Box -> IO Closure
getBoxedClosureData (Box a) = getClosureData a


-- This used to be available via GHC.Constants
#include "MachDeps.h"
wORD_SIZE, tAG_MASK, wORD_SIZE_IN_BITS :: Int
wORD_SIZE = SIZEOF_HSWORD
tAG_MASK = (1 `shift` TAG_BITS) - 1
wORD_SIZE_IN_BITS = WORD_SIZE_IN_BITS
