-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.ExecutionStack.Internal
-- Copyright   :  (c) The University of Glasgow 2013-2015
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC Extensions)
--
-- Internals of the `GHC.ExecutionStack` module
--
-- /Since: 4.11.0.0/
-----------------------------------------------------------------------------

{-# LANGUAGE UnboxedTuples, MagicHash, RecordWildCards #-}
module GHC.ExecutionStack.Internal (
  -- * Internal
    currentStackFrames
  , showStackFrames
  , currentExecutionStack
  , codemapTryUnload
  , codemapIsLoaded
  , withCodemap
  , getStackFrames
  , getStackFramesNoSync
  , StackFrame (..)
  ) where

import GHC.IO (IO(..))
import GHC.Base (Int(I##))
import qualified GHC.ExecutionStack.ZDecode as ZDecode
import GHC.Ptr (Ptr(Ptr))
import GHC.Prim (ByteArray##, sizeofByteArray##, indexAddrArray##)
import GHC.Prim (reifyStack##)
import Foreign.C.String (peekCString, CString)
import Foreign.Ptr (nullPtr)
import Foreign.Storable (Storable(..))
import Foreign.Marshal (alloca)
import Text.Printf (printf)
import Control.Exception.Base (bracket_)

#include "Rts.h"

-- | An 'ExecutionStack' represents a reified stack at some moment and each
-- element is a code address.
--
data ExecutionStack = ExecutionStack
    { unExecutionStack ::  ByteArray##
    }

-- | The number of functions on your stack
stackSize :: ExecutionStack -> Int
stackSize stack =
    I## (sizeofByteArray## (unExecutionStack stack)) `div` (#const SIZEOF_HSPTR)

stackIndex :: ExecutionStack -> Int -> Ptr Instruction
stackIndex (ExecutionStack ba##) (I## i##) = Ptr (indexAddrArray## ba## i##)

stackIndices :: ExecutionStack -> [Ptr Instruction]
stackIndices stack = map (stackIndex stack) [0..(stackSize stack)-1]

data StackFrame = StackFrame
    { unitName      :: !String -- ^ From symbol table
    , procedureName :: !String -- ^ From symbol table
    -- Once we have some more interesting data here, like with dwarf data, it
    -- might make sense to export this function and getStackFrames
    } deriving Show

-- | Like 'show', without @unlines@
prepareStackFrame :: StackFrame -> [String]
prepareStackFrame su =
        [ZDecode.decode $ procedureName su]
    --  Note: We intend to have multiple lines per frame once we have dwarf

-- | Pretty-print an execution stack:
--
-- @
-- Stack trace (Haskell):
--    0: base_GHCziExecutionStackziInternal_currentStackFrames1_info
--    1: base_GHCziBase_bindIO1_info
--    2: base_GHCziIO_unsafeDupablePerformIO_info
--    3: sPd_info
--    4: base_GHCziShow_zdfShowZLZRzuzdcshow_info
--    5: sPe_info
--    6: base_GHCziBase_eqString_info
--    7: Main_dontInlineMe_info
--    8: stg_bh_upd_frame_info
--    9: base_GHCziShow_showLitString_info
--   10: s2YV_info
--   11: base_GHCziIOziHandleziText_zdwa8_info
--   12: stg_catch_frame_info
-- @
--
-- For a program looking like this
--
-- @
-- module Main where
--
-- import GHC.ExecutionStack
-- import System.IO.Unsafe (unsafePerformIO)
--
-- main :: IO ()
-- main = print (dontInlineMe (show (unsafePerformIO printStack)))
--
-- printStack :: IO ()
-- printStack = currentStackFrames >>= (putStrLn . showStackFrames)
--
-- dontInlineMe :: String -> String
-- dontInlineMe x = case x of
--                    "hello" -> "world"
--                    x       -> x
-- @
--
-- As can be seen, the stack trace reveals function names.
--
showStackFrames :: [StackFrame] -> String
showStackFrames frames =
    "Stack trace (Haskell):\n" ++
    concatMap (uncurry displayFrame) ([0..] `zip` frames)

-- | How one StackFrame is displayed in one stack trace
displayFrame :: Int -> StackFrame -> String
displayFrame ix frame = unlines $ zipWith ($) formatters strings
      where formatters = (printf "%4u: %s" (ix :: Int)) : repeat ("      " ++)
            strings    = prepareStackFrame frame

-- We use these three empty data declarations for type-safety
data CodemapUnit
data CodemapProc
data Instruction

peekCodemapUnitName :: Ptr CodemapUnit -> IO CString
peekCodemapUnitName ptr = #{peek struct CodemapUnit_, name } ptr

peekCodemapProcName :: Ptr CodemapProc -> IO CString
peekCodemapProcName ptr = #{peek struct CodemapProc_, name } ptr

currentStackFrames :: IO [StackFrame]
currentStackFrames = currentExecutionStack >>= getStackFrames

-- | Reify the stack. This is the only way to get an ExecutionStack value.
currentExecutionStack :: IO (ExecutionStack)
currentExecutionStack = currentExecutionStackLimit (maxBound :: Int)

currentExecutionStackLimit :: Int -> IO (ExecutionStack)
currentExecutionStackLimit (I## i##) =
    IO (\s -> let (## new_s, byteArray## ##) = reifyStack## i## s
                  ba = ExecutionStack byteArray##
              in (## new_s, ba ##) )

-- | Tell the codemap module that you want to use codemap. Synchronized.
foreign import ccall "Codemap.h codemap_inc_ref" codemapIncRef :: IO ()

-- | Tell the codemap module that you are done using codemap. Synchronized.
foreign import ccall "Codemap.h codemap_dec_ref" codemapDecRef :: IO ()

-- | Ask the codemap module if it can unload and free up memory. It will not be
-- able to if the module is in use or if data is not loaded. Synchronized.
--
-- Returns True if codemap data was unloaded.
foreign import ccall "Codemap.h codemap_try_unload" codemapTryUnload :: IO Bool

foreign import ccall "Codemap.h codemap_is_loaded" codemapIsLoaded :: IO Bool

-- | Lookup an instruction pointer
--
-- Codemap module must be loaded to use this!
foreign import ccall "Codemap.h codemap_lookup_ip"
    codemapLookupIp ::
       Ptr Instruction -- ^ Code address you want information about
    -> Ptr (Ptr CodemapProc) -- ^ Out: CodemapProc Pointer Pointer
    -> Ptr (Ptr CodemapUnit) -- ^ Out: CodemapUnit Pointer Pointer
    -> IO ()

withCodemap :: IO a -> IO a
withCodemap = bracket_ codemapIncRef codemapDecRef

getStackFrameNoSync ::
       Ptr Instruction -- ^ Instruction Pointer
    -> IO StackFrame -- ^ Result
getStackFrameNoSync ip = do
    alloca $ \ppCodemapProc -> do
      poke ppCodemapProc nullPtr
      alloca $ \ppCodemapUnit -> do
          codemapLookupIp ip
                        ppCodemapProc
                        ppCodemapUnit
          pCodemapProc <- peek ppCodemapProc
          pCodemapUnit <- peek ppCodemapUnit
          unitName <- stringPeekWith peekCodemapUnitName pCodemapUnit
          procedureName <- stringPeekWith peekCodemapProcName pCodemapProc
          return StackFrame{..}

-- Note: if you grepped your way to the string "<Data not found>,
-- you probably forgot to compile that module with the `-g` flag to ghc.
stringPeekWith :: (Ptr a -> IO CString) -> Ptr a -> IO String
stringPeekWith _peeker ptr | ptr == nullPtr = return "<Data not found>"
stringPeekWith peeker ptr  | otherwise      = peeker ptr >>= peekCString

getStackFrames :: ExecutionStack -> IO [StackFrame]
getStackFrames stack = withCodemap $ getStackFramesNoSync stack

getStackFramesNoSync :: ExecutionStack -> IO [StackFrame]
getStackFramesNoSync = mapM getStackFrameNoSync . stackIndices
