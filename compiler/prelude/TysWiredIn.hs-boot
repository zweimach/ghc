module TysWiredIn where

import Name
import TyCon
import {-# SOURCE #-} TyCoRep    (Type, Kind)


typeNatKind, typeSymbolKind :: Type
mkBoxedTupleTy :: [Type] -> Type

levityTy, unliftedDataConTy :: Type

isLiftedTypeKindTyConName :: Name -> Bool

liftedTypeKind :: Kind

coercibleTyCon :: TyCon
