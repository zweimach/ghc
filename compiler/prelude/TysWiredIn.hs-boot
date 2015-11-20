module TysWiredIn where

import Name
import {-# SOURCE #-} TyCoRep    (Type, Kind)


typeNatKind, typeSymbolKind :: Type
mkBoxedTupleTy :: [Type] -> Type

levityTy, unliftedDataConTy :: Type

isLiftedTypeKindTyConName :: Name -> Bool

liftedTypeKind :: Kind
