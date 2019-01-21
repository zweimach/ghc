{-# LANGUAGE TemplateHaskell #-}

module T10047C where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

x = $(varE (mkNameG_d "base" "GHC.Base" "id"))
