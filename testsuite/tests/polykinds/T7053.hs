{-# LANGUAGE PolyKinds, GADTs #-}

module T7053 where

-- no standalone kind signature
data TypeRep (a :: k) where
   TyApp   :: TypeRep a -> TypeRep b -> TypeRep (a b)

