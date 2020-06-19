{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts #-}

module FunDepOrigin1 where

class C a b | a -> b where
  op :: a -> b -> b

foo _ = op True Nothing

bar _ = op False []

-- See Note [Suppressing confusing errors] in GHC.Tc.Errors
