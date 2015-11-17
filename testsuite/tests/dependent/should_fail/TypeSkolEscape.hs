module TypeSkolEscape where

import GHC.Exts

type Bad = forall (v :: Levity) (a :: TYPE v). a
