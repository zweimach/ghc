{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneKindSignatures #-}
module T7892 where

import Data.Kind

type C :: (Type -> Type) -> Constraint
class C f where
   type F (f :: Type) :: Type


