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

module GHC.ExecutionStack.Internal (
  -- * Internal
    Location (..)
  , SrcLoc (..)
  , StackTrace
  , stackFrames
  , stackDepth
  , collectStackTrace
  , showStackFrames
  ) where

import Data.Word
import Foreign.C.String (peekCString)
import Foreign.C.Types (CChar)
import Foreign.Ptr (Ptr, nullPtr, castPtr, plusPtr, FunPtr)
import Foreign.ForeignPtr
import Foreign.ForeignPtr.Unsafe
import Foreign.Storable (Storable(..))
import System.IO.Unsafe (unsafePerformIO)

#include "Rts.h"

-- | A location in the original program source.
data SrcLoc = SrcLoc { sourceFile   :: String
                     , sourceLine   :: Int
                     , sourceColumn :: Int
                     }

-- | Location information about an addresss from a backtrace.
data Location = Location { objectName   :: String
                         , functionName :: String
                         , srcLoc       :: Maybe SrcLoc
                         }

newtype StackTrace = StackTrace (ForeignPtr StackTrace)

-- | How many stack frames in the given stack trace.
stackDepth :: StackTrace -> Int
stackDepth (StackTrace fptr) = unsafePerformIO $
    withForeignPtr fptr $ \ptr -> fromIntegral `fmap` peekWord (castPtr ptr)
  where
    peekWord = peek :: Ptr Word -> IO Word

firstFrame :: StackTrace -> Ptr Location
firstFrame (StackTrace fptr) =
    ptr `plusPtr` sizeOf (undefined :: Word)
  where ptr = unsafeForeignPtrToPtr fptr

peekLocation :: Ptr Location -> IO Location
peekLocation ptr = do
    let ptrSize = sizeOf ptr
        peekCStringPtr :: Ptr (Ptr CChar) -> IO String
        peekCStringPtr p = do
            str <- peek p
            if str /= nullPtr
              then peekCString str
              else return ""
    objFile <- peekCStringPtr (castPtr ptr)
    function <- peekCStringPtr (castPtr ptr `plusPtr` (1*ptrSize))
    srcFile <- peekCStringPtr (castPtr ptr `plusPtr` (2*ptrSize))
    lineNo <- peek (castPtr ptr `plusPtr` (3*ptrSize)) :: IO Word32
    colNo <- peek (castPtr ptr `plusPtr` (3*ptrSize + sizeOf lineNo)) :: IO Word32
    let srcLoc
          | null srcFile = Nothing
          | otherwise = Just $ SrcLoc { sourceFile = srcFile
                                      , sourceLine = fromIntegral lineNo
                                      , sourceColumn = fromIntegral colNo
                                      }
    return Location { objectName = objFile
                    , functionName = function
                    , srcLoc = srcLoc
                    }

-- | The size in bytes of a 'locationSize'
locationSize :: Int
locationSize = 2*4 + 4*ptrSize
  where ptrSize = sizeOf (undefined :: Ptr ())

-- | List the frames of a stack trace.
stackFrames :: StackTrace -> [Location]
stackFrames st@(StackTrace fptr) =
    iterFrames (stackDepth st - 1) (firstFrame st)
  where
    wordSize = sizeOf (0 :: Word)
    ptr = unsafeForeignPtrToPtr fptr

    stackLen = stackDepth st

    iterFrames :: Int -> Ptr Location -> [Location]
    iterFrames (-1) _     = []
    iterFrames n    frame =
        unsafePerformIO this : iterFrames (n-1) frame'
      where
        this = withForeignPtr fptr $ const $ peekLocation frame
        frame' = frame `plusPtr` locationSize

foreign import ccall unsafe "libdw_my_cap_get_backtrace"
    libdw_my_cap_get_backtrace :: IO (Ptr StackTrace)

foreign import ccall unsafe "libdw_my_cap_free"
    libdw_my_cap_free :: IO ()

foreign import ccall unsafe "&backtrace_free"
    freeStackTrace :: FunPtr (Ptr StackTrace -> IO ())

-- | Get an execution stack.
collectStackTrace :: IO StackTrace
collectStackTrace = do
    st <- libdw_my_cap_get_backtrace
    StackTrace <$> newForeignPtr freeStackTrace st

invalidateDebugCache :: IO ()
invalidateDebugCache = libdw_my_cap_free

showStackFrames :: [Location] -> ShowS
showStackFrames frames =
    showString "Stack trace:\n"
    . foldr (.) id (map showFrame frames)
  where
    showFrame :: Location -> ShowS
    showFrame frame =
      showString "    "
      . showString (functionName frame)
      . maybe id showSrcLoc (srcLoc frame)
      . showString " in "
      . showString (objectName frame)
      . showString "\n"

    showSrcLoc :: SrcLoc -> ShowS
    showSrcLoc loc =
        showString " ("
      . showString (sourceFile loc)
      . showString ":"
      . showString (show $ sourceLine loc)
      . showString "."
      . showString (show $ sourceColumn loc)
      . showString ")"
