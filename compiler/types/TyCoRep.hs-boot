module TyCoRep where

import Outputable (Outputable)

data Type
data Binder
data TyThing
data Coercion
data LeftOrRight
data UnivCoProvenance

type PredType = Type
type Kind = Type

instance Outputable Type
