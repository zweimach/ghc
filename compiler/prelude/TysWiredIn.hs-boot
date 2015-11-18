module TysWiredIn where

import Name
import {-# SOURCE #-} TyCon      (TyCon)
import {-# SOURCE #-} TyCoRep    (Type, Kind)


eqTyCon, coercibleTyCon :: TyCon
typeNatKind, typeSymbolKind :: Type
mkBoxedTupleTy :: [Type] -> Type

levityTy, unliftedDataConTy :: Type

isLiftedTypeKindTyConName :: Name -> Bool

liftedTypeKind :: Kind
