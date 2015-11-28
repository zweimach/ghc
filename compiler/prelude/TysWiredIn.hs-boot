module TysWiredIn where

import {-# SOURCE #-} TyCoRep    (Type, Kind)


typeNatKind, typeSymbolKind :: Type
mkBoxedTupleTy :: [Type] -> Type

levityTy, unliftedDataConTy :: Type

liftedTypeKind :: Kind
