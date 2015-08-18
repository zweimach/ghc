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
--      stackFrames <- currentStackFrames
--      putStrLn $ showStackFrames stackFrames
-- @
--
-- Your `ghc` must have been built with libelf for this to work.
--
-- @
-- $ ghc --info | grep libelf
--  ,("RTS expects libelf","YES")
-- @
--
-- /Since: 4.11.0.0/
-----------------------------------------------------------------------------

module GHC.ExecutionStack (
    currentStackFrames
  , showStackFrames
  ) where

import GHC.ExecutionStack.Internal (currentStackFrames, showStackFrames)
