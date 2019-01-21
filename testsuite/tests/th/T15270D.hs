{-# LANGUAGE TemplateHaskell #-}

module T10047D where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

x = $(conE (mkNameG_v "ghc-prim" "GHC.Types" "True"))
