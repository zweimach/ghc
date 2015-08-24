{-# LANGUAGE CPP #-}

-----------------------------------------------------------------------------
--
-- Generate .debug_ghc section
--
-- Association of debug data on the Cmm level, with methods to encode it in
-- event log format for later inclusion in profiling event logs.
--
-----------------------------------------------------------------------------

module Debug.GhcDebug (writeDebugToEventlog) where

import Binary
import BlockId         ( blockLbl )
import CLabel
import Cmm
import CmmUtils
import CoreSyn
import FastString      ( nilFS, mkFastString )
import Debug
import DynFlags
import FastString      ( nilFS, mkFastString, unpackFS )
import Module
import Outputable
import PprCore         ()
import PprCmmExpr      ( pprExpr )
import SrcLoc
import UniqFM
import Util
import Var             ( Var, varType )

import Compiler.Hoopl

import Control.Monad   ( foldM, forM_, void, when )

import Data.Char       ( ord)
import Data.Maybe
import Data.List     ( find, minimumBy )
import Data.Ord      ( comparing )
import Data.List       ( find, minimumBy )
import Data.Ord        ( comparing )
import qualified Data.Map as Map
import Data.Word       ( Word8, Word16 )

import Foreign.ForeignPtr

#define EVENTLOG_CONSTANTS_ONLY
#include "../../includes/rts/EventLogFormat.h"

-- | Generates debug data into a buffer
writeDebugToEventlog :: DynFlags -> ModLocation -> [DebugBlock] -> IO (Int, ForeignPtr Word8)
writeDebugToEventlog dflags mod_loc blocks = do

  -- Write data into a binary memory handle
  bh <- openBinMem $ 1024 * 1024
  let code = do putEvent EVENT_DEBUG_MODULE $ do
                  putString $ packageIdString (thisPackage dflags)
                  putString $ fromMaybe "???" $ ml_hs_file mod_loc
                foldM (putBlock maxBound) 0 blocks
  void $ runPutDbg code bh dflags emptyUFM
  getBinMemBuf bh

-- | Packs the given static value into a (variable-length) event-log
-- packet.
putEvent :: Word8 -> PutDbgM () -> PutDbgM ()
putEvent id cts
  = PutDbgM $ \bh df cm ->
     let wrap = do
           put_ bh id
           -- Put placeholder for size
           sizePos <- put bh (0 :: Word16)
           -- Put contents
           res <- runPutDbg cts bh df cm
           -- Put final size
           endPos <- tellBin bh
           putAt bh sizePos $ fromIntegral $ (endPos `diffBin` sizePos) - 2
           -- Seek back
           seekBin bh endPos
           return res
     in do catchSize bh 0x10000 wrap (return (cm, ()))

-- | Puts an alternate version if the first one is bigger than the
-- given limit.
--
-- This is a pretty crude way of handling oversized
-- packets... Can't think of a better way right now though.
catchSize :: BinHandle -> Int -> IO a -> IO a -> IO a
catchSize bh limit cts1 cts2 = do

  -- Put contents, note how much size it uses
  start <- tellBin bh :: IO (Bin ())
  a <- cts1
  end <- tellBin bh

  -- Seek back and put second version if size is over limit
  if (end `diffBin` start) >= limit
    then seekBin bh start >> cts2
    else return a

type BlockId = Word16

putBlock :: BlockId -> BlockId -> DebugBlock -> PutDbgM BlockId
putBlock pid bid block = do
  -- Put sub-blocks
  bid' <- foldM (putBlock bid) (bid+1) (dblBlocks block)
  -- Write our own data
  putEvent EVENT_DEBUG_BLOCK $ do
    putDbg bid
    putDbg pid
    dflags <- getDynFlags
    let showSDocC = flip (renderWithStyle dflags) (mkCodeStyle CStyle)
    putString $ showSDocC $ ppr (dblCLabel block)
  -- Write annotations.
  mapM_ putAnnotEvent (dblTicks block)
  return bid'

putAnnotEvent :: CmmTickish -> PutDbgM ()
putAnnotEvent (SourceNote ss names) =
  putEvent EVENT_DEBUG_SOURCE $ do
    putDbg $ encLoc $ srcSpanStartLine ss
    putDbg $ encLoc $ srcSpanStartCol ss
    putDbg $ encLoc $ srcSpanEndLine ss
    putDbg $ encLoc $ srcSpanEndCol ss
    putString $ unpackFS $ srcSpanFile ss
    putString names
 where encLoc x = fromIntegral x :: Word16

putAnnotEvent (CoreNote lbl corePtr)
  -- This piece of core was already covered earlier in this block?
  = do elem <- elemCoreMap (lbl, exprPtrCons corePtr)
       when (not elem) $ putEvent EVENT_DEBUG_CORE $ do
         dflags <- getDynFlags
         putString $ showSDocDump dflags $ ppr lbl
         -- Emit core, leaving out (= referencing) any core pieces
         -- that were emitted from sub-blocks
         case corePtr of
           ExprPtr core -> putCoreExpr core
           AltPtr  alt  -> putCoreAlt alt

putAnnotEvent _ = return ()

-- | Constants for core binary representation
coreMisc, coreApp, coreRef, coreLam, coreLet, coreCase, coreAlt :: Word8
coreMisc = 0
coreApp  = 1
coreRef  = 2
coreLam  = 3
coreLet  = 4
coreCase = 5
coreAlt  = 6

type CoreMap = UniqFM [AltCon]
newtype PutDbgM a = PutDbgM { runPutDbg :: BinHandle -> DynFlags -> CoreMap -> IO (CoreMap, a) }

instance Functor PutDbgM where
  fmap f m = PutDbgM $ \bh df cm -> runPutDbg m bh df cm >>= \(cm', a) -> return (cm', f a)
instance Monad PutDbgM where
  return x = PutDbgM $ \_ _ cm -> return (cm, x)
  m >>= f = PutDbgM $ \bh df cm -> runPutDbg m bh df cm >>= \(cm', a) -> runPutDbg (f a) bh df cm'

instance HasDynFlags PutDbgM where
  getDynFlags = PutDbgM $ \_ df cm -> return (cm,df)

putDbg :: Binary a => a -> PutDbgM ()
putDbg x = PutDbgM $ \bf _ cm -> put_ bf x >> return (cm,())

-- | Put a C-style string (null-terminated). We assume that the string
-- is ASCII.
--
-- This could well be subject to change in future...
putString :: String -> PutDbgM ()
putString str = do
  let putByte = putDbg :: Word8 -> PutDbgM ()
  mapM_ (putByte . fromIntegral . ord) str
  putByte 0

putSDoc :: SDoc -> PutDbgM ()
putSDoc str = do
  dflags <- getDynFlags
  putString $ showSDoc dflags str

elemCoreMap :: (Var, AltCon) -> PutDbgM Bool
elemCoreMap (bind, con) = PutDbgM $ \_ _ cm -> return $ (,) cm $
  case lookupUFM cm bind of
    Just cs -> con `elem` cs
    Nothing -> False

addToCoreMap :: Var -> AltCon -> PutDbgM ()
addToCoreMap b a = PutDbgM $ \_ _ cm -> return (addToUFM_C (\o _ -> a:o) cm b [a], ())

putCoreExpr :: CoreExpr -> PutDbgM ()
putCoreExpr (App e1 e2) = do
  putDbg coreApp
  putCoreExpr e1
  putCoreExpr e2
putCoreExpr (Lam b e) = do
  putDbg coreLam
  putSDoc $ ppr b
  putSDoc $ ppr $ varType b
  putCoreExpr e
putCoreExpr (Let es e) = do
  putDbg coreLet
  putCoreLet es
  putCoreExpr e
putCoreExpr (Case expr bind _ alts) = do
  putDbg coreCase
  putCoreExpr expr
  putSDoc $ ppr bind
  putSDoc $ ppr $ varType bind
  putDbg (fromIntegral (length alts) :: Word16)
  forM_ alts $ \alt@(a, _, _) ->
    checkCoreRef (bind, a) $
      putCoreAlt alt
putCoreExpr (Cast e _) = putCoreExpr e
putCoreExpr (Tick _ e) = putCoreExpr e
-- All other elements are supposed to have a simple "pretty printed"
-- representation that we can simply output verbatim.
putCoreExpr other = do
  putDbg coreMisc
  putSDoc $ ppr other

putCoreAlt :: CoreAlt -> PutDbgM ()
putCoreAlt (a,binds,e) = do
  putDbg coreAlt
  putSDoc $ case a of
    DEFAULT -> empty
    _       -> ppr a
  putDbg (fromIntegral (length binds) :: Word16)
  forM_ binds $ \b -> do
    putSDoc . ppr $ b
    putSDoc . ppr . varType $ b
  putCoreExpr e

putCoreLet :: CoreBind -> PutDbgM ()
putCoreLet (NonRec b e) = do
  putDbg (1 :: Word16) -- could use 0 to mark non-recursive case?
  putSDoc $ ppr b
  putSDoc $ ppr $ varType b
  checkCoreRef (b, DEFAULT) $ putCoreExpr e
putCoreLet (Rec ps) = do
  putDbg (fromIntegral $ length ps :: Word16)
  forM_ ps $ \(b, e) -> do
    putSDoc $ ppr b
    putSDoc $ ppr $ varType b
    checkCoreRef (b, DEFAULT) $ putCoreExpr e

-- | Generate reference to core piece that was output elsewhere... Or
-- proceed with given code otherwise.
checkCoreRef :: (Var, AltCon) -> PutDbgM () -> PutDbgM ()
checkCoreRef (b,a) code = do
  elem <- elemCoreMap (b,a)
  if elem
    then do putDbg coreRef
            dflags <- getDynFlags
            putString $ showSDocDump dflags $ ppr b
            putSDoc $ case a of
              DEFAULT -> empty
              _       -> ppr a
    else do addToCoreMap b a
            code
