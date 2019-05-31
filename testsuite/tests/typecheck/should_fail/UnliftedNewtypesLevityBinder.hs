{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module UnliftedNewtypesLevityBinder where

import GHC.Types (RuntimeRep,TYPE,Coercible)

type Ident :: forall (r :: RuntimeRep). TYPE r -> TYPE r
newtype Ident a where
  IdentC :: forall (r :: RuntimeRep) (a :: TYPE r). a -> Ident a

bad :: forall (r :: RuntimeRep) (a :: TYPE r). a -> Ident a
bad = IdentC
