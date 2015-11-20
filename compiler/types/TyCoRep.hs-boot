module TyCoRep where

import Outputable (Outputable)
import Data.Data (Data,Typeable)

data Type
data Binder
data TyThing
data Coercion
data LeftOrRight
data UnivCoProvenance
data TCvSubst

type PredType = Type
type Kind = Type
type ThetaType = [PredType]

instance Outputable Type
instance Typeable Type
instance Data Type
