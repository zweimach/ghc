{-# LANGUAGE RankNTypes, PolyKinds #-}

module TypeSkolEscape where

import GHC.Types
import GHC.Exts

type Bad = forall (v :: Levity) (a :: TYPE v). a
