module Coercion where

import {-# SOURCE #-} TyCoRep
import {-# SOURCE #-} CoAxiom
import {-# SOURCE #-} TyCon
import Var
import VarEnv
import Outputable
import Pair
import FastString

mkReflCo :: Role -> Type -> Coercion
mkTyConAppCo :: Role -> TyCon -> [CoercionArg] -> Coercion
mkAppCo :: Coercion -> Coercion -> CoercionArg -> Coercion
mkForAllCo :: ForAllCoBndr -> Coercion -> Coercion
mkCoVarCo :: CoVar -> Coercion
mkAxiomInstCo :: CoAxiom Branched -> BranchIndex -> [CoercionArg] -> Coercion
mkPhantomCo :: Coercion -> Type -> Type -> Coercion
mkUnsafeCo :: FastString -> Role -> Type -> Type -> Coercion
mkSymCo :: Coercion -> Coercion
mkTransCo :: Coercion -> Coercion -> Coercion
mkNthCo :: Int -> Coercion -> Coercion
mkLRCo :: LeftOrRight -> Coercion -> Coercion
mkInstCo :: Coercion -> CoercionArg -> Coercion
mkCoherenceCo :: Coercion -> Coercion -> Coercion
mkKindCo :: Coercion -> Coercion
mkKindAppCo :: Coercion -> Coercion
mkSubCo :: Coercion -> Coercion

mkFunCos :: Role -> [Coercion] -> Coercion -> Coercion

isReflCo :: Coercion -> Bool
coVarKindsTypesRole :: CoVar -> (Kind, Kind, Type, Type, Role)
coVarRole :: CoVar -> Role
mkFreshCoVarOfType :: InScopeSet -> Type -> CoVar

mkHomoCoBndr :: TyCoVar -> ForAllCoBndr
mkTyHeteroCoBndr :: Coercion -> TyVar -> TyVar -> CoVar -> ForAllCoBndr
mkCoHeteroCoBndr :: Coercion -> CoVar -> CoVar -> ForAllCoBndr
getHomoVar_maybe :: ForAllCoBndr -> Maybe TyCoVar
splitHeteroCoBndr_maybe :: ForAllCoBndr -> Maybe (Coercion, TyCoVar, TyCoVar)

mkCoercionType :: Role -> Type -> Type -> Type

data LiftingContext
liftCoSubst :: Role -> LiftingContext -> Type -> Coercion
coercionSize :: Coercion -> Int
seqCo :: Coercion -> ()

coercionKind :: Coercion -> Pair Type
coercionType :: Coercion -> Type

pprCo :: Coercion -> SDoc
pprCoBndr :: ForAllCoBndr -> SDoc
pprCoArg :: CoercionArg -> SDoc


