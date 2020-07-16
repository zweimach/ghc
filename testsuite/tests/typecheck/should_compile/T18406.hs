{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts #-}

module Bug where

class C a b | a -> b where
  op :: a -> b -> ()

f x = op True x
