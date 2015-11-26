{-# LANGUAGE NoImplicitPrelude #-}

module GHC.ExecutionStack.Internal (
    StackTrace
  , collectStackTrace
  ) where

import GHC.Base

data StackTrace

collectStackTrace :: IO (Maybe StackTrace)
