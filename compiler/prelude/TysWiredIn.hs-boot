module TysWiredIn where

import TyCon
import {-# SOURCE #-} TyCoRep    (Type, Kind)


typeNatKind, typeSymbolKind :: Type
mkBoxedTupleTy :: [Type] -> Type

levityTy, unliftedDataConTy :: Type

liftedTypeKind :: Kind

coercibleTyCon :: TyCon
