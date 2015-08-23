-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.ExecutionStack
-- Copyright   :  (c) The University of Glasgow 2013-2015
-- License     :  see libraries/base/LICENSE
--
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC Extensions)
--
-- This is a module for efficient stack traces. This stack trace implementation
-- is considered low overhead. Basic usage looks like this:
--
-- @
-- import GHC.ExecutionStack
--
-- myFunction :: IO ()
-- myFunction = do
--      putStrLn =<< showStackTrace stackFrames
-- @
--
-- Your GHC must have been built with @libdw@ support for this to work.
--
-- @
-- $ ghc --info | grep libdw
--  ,("RTS expects libdw","YES")
-- @
--
-- /Since: 4.11.0.0/
-----------------------------------------------------------------------------

module GHC.ExecutionStack (
    Location (..)
  , SrcLoc (..)
  , getStackTrace
  , showStackTrace
  ) where

import GHC.ExecutionStack.Internal

-- | Get a trace of the current execution stack state.
getStackTrace :: IO [Location]
getStackTrace = stackFrames `fmap` collectStackTrace

-- | Get a string representation of the current execution stack state.
showStackTrace :: IO String
showStackTrace = flip showStackFrames "" `fmap` getStackTrace
