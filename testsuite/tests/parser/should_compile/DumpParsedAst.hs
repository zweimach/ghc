{-# LANGUAGE DataKinds, PolyKinds, TypeOperators, TypeFamilies,
             TypeApplications, StandaloneKindSignatures #-}

module DumpParsedAst where
import Data.Kind

data Peano = Zero | Succ Peano

type Length :: [k] -> Peano
type family Length (as :: [k]) :: Peano where
  Length (a : as) = Succ (Length as)
  Length '[]      = Zero

-- vis kind app
data T f (a :: k) = MkT (f a)

type F1 :: k -> (k -> Type) -> Type
type family F1 (a :: k) (f :: k -> Type) :: Type where
  F1 @Peano a f = T @Peano f a

main = putStrLn "hello"
