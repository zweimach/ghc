module Coercion where

import {-# SOURCE #-} TyCoRep
import {-# SOURCE #-} CoAxiom
import {-# SOURCE #-} TyCon
import Var
import VarEnv
import Outputable
import Pair

mkReflCo :: Role -> Type -> Coercion
mkTyConAppCo :: Role -> TyCon -> [Coercion] -> Coercion
mkAppCo :: Coercion -> Coercion -> Coercion -> Coercion
mkForAllCo :: ForAllCoBndr -> Coercion -> Coercion
mkCoVarCo :: CoVar -> Coercion
mkAxiomInstCo :: CoAxiom Branched -> BranchIndex -> [Coercion] -> Coercion
mkPhantomCo :: Coercion -> Type -> Type -> Coercion
mkUnsafeCo :: Role -> Type -> Type -> Coercion
mkUnivCo :: UnivCoProvenance -> Role -> Coercion -> Type -> Type -> Coercion
mkSymCo :: Coercion -> Coercion
mkTransCo :: Coercion -> Coercion -> Coercion
mkNthCo :: Int -> Coercion -> Coercion
mkLRCo :: LeftOrRight -> Coercion -> Coercion
mkInstCo :: Coercion -> Coercion -> Coercion
mkCoherenceCo :: Coercion -> Coercion -> Coercion
mkKindCo :: Coercion -> Coercion
mkKindAppCo :: Coercion -> Coercion
mkSubCo :: Coercion -> Coercion
mkProofIrrelCo :: Role -> Coercion -> Coercion -> Coercion -> Coercion

mkFunCos :: Role -> [Coercion] -> Coercion -> Coercion

isReflCo :: Coercion -> Bool
coVarKindsTypesRole :: CoVar -> (Kind, Kind, Type, Type, Role)
coVarRole :: CoVar -> Role
mkFreshCoVarOfType :: InScopeSet -> Type -> CoVar

coBndrKindCo   :: ForAllCoBndr -> Coercion
mkForAllCoBndr :: Coercion -> TyVar -> TyVar -> CoVar -> ForAllCoBndr

mkCoercionType :: Role -> Type -> Type -> Type

data LiftingContext
liftCoSubst :: Role -> LiftingContext -> Type -> Coercion
coercionSize :: Coercion -> Int
seqCo :: Coercion -> ()

coercionKind :: Coercion -> Pair Type
coercionType :: Coercion -> Type

pprCo :: Coercion -> SDoc
pprCoBndr :: ForAllCoBndr -> SDoc
