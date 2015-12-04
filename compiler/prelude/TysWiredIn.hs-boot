module TysWiredIn where

import {-# SOURCE #-} TyCoRep    (Type, Kind)


listTyCon :: TyCon
typeNatKind, typeSymbolKind :: Type
mkBoxedTupleTy :: [Type] -> Type

levityTy, unliftedDataConTy :: Type

liftedTypeKind :: Kind
