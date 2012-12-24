%
% (c) The University of Glasgow 2006
%

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details

-- | Module for (a) type kinds and (b) type coercions, 
-- as used in System FC. See 'CoreSyn.Expr' for
-- more on System FC and how coercions fit into it.
--
module Coercion (
        -- * Main data type
        Coercion(..), Var, CoVar,
        LeftOrRight(..), pickLR,

        -- ** Functions over coercions
        coVarTypes, coVarKind,
        coercionType, coercionKind, coercionKinds, isReflCo,
        isReflCo_maybe,
        mkCoercionType,

	-- ** Constructing coercions
        mkReflCo, mkCoVarCo, 
        mkAxInstCo, mkSingletonAxInstCo, mkAxInstRHS,
        mkSingletonAxInstRHS,
        mkPiCo, mkPiCos, mkCoCast,
        mkSymCo, mkTransCo, mkNthCo, mkLRCo,
	mkInstCo, mkAppCo, mkTyConAppCo, mkFunCo,
        mkForAllCo, mkUnsafeCo,
        mkNewTypeCo, 

        -- ** Decomposition
        splitNewTypeRepCo_maybe, instNewTyCon_maybe, decomposeCo,
        getCoVar_maybe,

        splitTyConAppCo_maybe,
        splitAppCo_maybe,
        splitForAllCo_maybe,

	-- ** Coercion variables
	mkCoVar, isCoVar, isCoVarType, coVarName, setCoVarName, setCoVarUnique,

        -- ** Free variables
        tyCoVarsOfCo, tyCoVarsOfCos, coVarsOfCo, coercionSize,
	
        -- ** Substitution
        CvSubstEnv, emptyCvSubstEnv, 
 	lookupCoVar,
	zapCvSubstEnv, getCvInScope,
        substCo, substCos, substCoVar, substCoVars,
        substCoWithTy, substCoWithTys, 
	substCoVarBndr,

	-- ** Lifting
	liftCoMatch, liftCoSubstTyVar, liftCoSubstWith, 
        
        -- ** Comparison
        coreEqCoercion, coreEqCoercion2,

        -- ** Forcing evaluation of coercions
        seqCo,
        
        -- * Pretty-printing
        pprCo, pprParendCo, pprCoAxiom, 

        -- * Other
        applyCo
       ) where 

#include "HsVersions.h"

import Unify	( MatchEnv(..), matchList )
import TypeRep
import qualified Type
import Type hiding( substTy, substTyVarBndr, extendTCvSubst )
import TyCon
import CoAxiom
import Var
import VarEnv
import VarSet
import Maybes   ( orElse )
import Name	( Name, NamedThing(..), nameUnique )
import OccName 	( parenSymOcc )
import Util
import BasicTypes
import Outputable
import Unique
import Pair
import PrelNames	( funTyConKey, eqPrimTyConKey )
import Control.Applicative
import Data.Traversable (traverse, sequenceA)
import Control.Arrow (second)
import FastString

import qualified Data.Data as Data hiding ( TyCon )
\end{code}

%************************************************************************
%*									*
\subsection{Coercion variables}
%*									*
%************************************************************************

\begin{code}
coVarName :: CoVar -> Name
coVarName = varName

setCoVarUnique :: CoVar -> Unique -> CoVar
setCoVarUnique = setVarUnique

setCoVarName :: CoVar -> Name -> CoVar
setCoVarName   = setVarName

isCoVar :: Var -> Bool
isCoVar v = isCoVarType (varType v)

isCoVarType :: Type -> Bool
isCoVarType ty 	    -- Tests for t1 ~# t2, the unboxed equality
  = case splitTyConApp_maybe ty of
      Just (tc,tys) -> tc `hasKey` eqPrimTyConKey && tys `lengthAtLeast` 4
      Nothing       -> False
\end{code}


\begin{code}
coercionSize :: Coercion -> Int
coercionSize (Refl ty)           = typeSize ty
coercionSize (TyConAppCo _ cos)  = 1 + sum (map coercionSize cos)
coercionSize (AppCo co1 co2)     = coercionSize co1 + coercionSize co2
coercionSize (ForAllCo _ co)     = 1 + coercionSize co
coercionSize (CoVarCo _)         = 1
coercionSize (AxiomInstCo _ _ cos) = 1 + sum (map coercionSize cos)
coercionSize (UnsafeCo ty1 ty2)  = typeSize ty1 + typeSize ty2
coercionSize (SymCo co)          = 1 + coercionSize co
coercionSize (TransCo co1 co2)   = 1 + coercionSize co1 + coercionSize co2
coercionSize (NthCo _ co)        = 1 + coercionSize co
coercionSize (LRCo  _ co)        = 1 + coercionSize co
coercionSize (InstCo co ty)      = 1 + coercionSize co + typeSize ty
\end{code}

%************************************************************************
%*									*
                   Pretty-printing coercions
%*                                                                      *
%************************************************************************

@pprCo@ is the standard @Coercion@ printer; the overloaded @ppr@
function is defined to use this.  @pprParendCo@ is the same, except it
puts parens around the type, except for the atomic cases.
@pprParendCo@ works just by setting the initial context precedence
very high.

\begin{code}
instance Outputable Coercion where
  ppr = pprCo

pprCo, pprParendCo :: Coercion -> SDoc
pprCo       co = ppr_co TopPrec   co
pprParendCo co = ppr_co TyConPrec co

ppr_co :: Prec -> Coercion -> SDoc
ppr_co _ (Refl ty) = angleBrackets (ppr ty)

ppr_co p co@(TyConAppCo tc [_,_])
  | tc `hasKey` funTyConKey = ppr_fun_co p co

ppr_co p (TyConAppCo tc cos)   = pprTcApp   p ppr_co tc cos
ppr_co p (AppCo co1 co2)       = maybeParen p TyConPrec $
                                 pprCo co1 <+> ppr_co TyConPrec co2
ppr_co p co@(ForAllCo {})      = ppr_forall_co p co
ppr_co _ (CoVarCo cv)          = parenSymOcc (getOccName cv) (ppr cv)
ppr_co p (AxiomInstCo con index cos)
  = angleBrackets (pprPrefixApp p 
                    (ppr (getName con) <> brackets (ppr index))
                    (map (ppr_co TyConPrec) cos))

ppr_co p co@(TransCo {}) = maybeParen p FunPrec $
                           case trans_co_list co [] of
                             [] -> panic "ppr_co"
                             (co:cos) -> sep ( ppr_co FunPrec co
                                             : [ char ';' <+> ppr_co FunPrec co | co <- cos])
ppr_co p (InstCo co ty) = maybeParen p TyConPrec $
                          pprParendCo co <> ptext (sLit "@") <> pprType ty

ppr_co p (UnsafeCo ty1 ty2) = pprPrefixApp p (ptext (sLit "UnsafeCo")) 
                                           [pprParendType ty1, pprParendType ty2]
ppr_co p (SymCo co)         = pprPrefixApp p (ptext (sLit "Sym")) [pprParendCo co]
ppr_co p (NthCo n co)       = pprPrefixApp p (ptext (sLit "Nth:") <> int n) [pprParendCo co]
ppr_co p (LRCo sel co)      = pprPrefixApp p (ppr sel) [pprParendCo co]

trans_co_list :: Coercion -> [Coercion] -> [Coercion]
trans_co_list (TransCo co1 co2) cos = trans_co_list co1 (trans_co_list co2 cos)
trans_co_list co                cos = co : cos

instance Outputable LeftOrRight where
  ppr CLeft    = ptext (sLit "Left")
  ppr CRight   = ptext (sLit "Right")

ppr_fun_co :: Prec -> Coercion -> SDoc
ppr_fun_co p co = pprArrowChain p (split co)
  where
    split :: Coercion -> [SDoc]
    split (TyConAppCo f [arg,res])
      | f `hasKey` funTyConKey
      = ppr_co FunPrec arg : split res
    split co = [ppr_co TopPrec co]

ppr_forall_co :: Prec -> Coercion -> SDoc
ppr_forall_co p ty
  = maybeParen p FunPrec $
    sep [pprForAll tvs, ppr_co TopPrec rho]
  where
    (tvs,  rho) = split1 [] ty
    split1 tvs (ForAllCo tv ty) = split1 (tv:tvs) ty
    split1 tvs ty               = (reverse tvs, ty)
\end{code}

\begin{code}
pprCoAxiom :: CoAxiom br -> SDoc
pprCoAxiom ax@(CoAxiom { co_ax_tc = tc, co_ax_branches = branches })
  = hang (ptext (sLit "axiom") <+> ppr ax <+> dcolon)
       2 (vcat (map (pprCoAxBranch tc) $ fromBranchList branches))

pprCoAxBranch :: TyCon -> CoAxBranch -> SDoc
pprCoAxBranch tc (CoAxBranch { cab_tvs = tvs, cab_lhs = lhs, cab_rhs = rhs })
  = ptext (sLit "forall") <+> pprTvBndrs tvs <> dot <+> 
      pprEqPred (Pair (mkTyConApp tc lhs) rhs)

\end{code}

%************************************************************************
%*									*
	Functions over Kinds		
%*									*
%************************************************************************

\begin{code}
-- | This breaks a 'Coercion' with type @T A B C ~ T D E F@ into
-- a list of 'Coercion's of kinds @A ~ D@, @B ~ E@ and @E ~ F@. Hence:
--
-- > decomposeCo 3 c = [nth 0 c, nth 1 c, nth 2 c]
decomposeCo :: Arity -> Coercion -> [Coercion]
decomposeCo arity co 
  = [mkNthCo n co | n <- [0..(arity-1)] ]
           -- Remember, Nth is zero-indexed

-- | Attempts to obtain the type variable underlying a 'Coercion'
getCoVar_maybe :: Coercion -> Maybe CoVar
getCoVar_maybe (CoVarCo cv) = Just cv  
getCoVar_maybe _            = Nothing

-- | Attempts to tease a coercion apart into a type constructor and the application
-- of a number of coercion arguments to that constructor
splitTyConAppCo_maybe :: Coercion -> Maybe (TyCon, [Coercion])
splitTyConAppCo_maybe (Refl ty)           = (fmap . second . map) Refl (splitTyConApp_maybe ty)
splitTyConAppCo_maybe (TyConAppCo tc cos) = Just (tc, cos)
splitTyConAppCo_maybe _                   = Nothing

splitAppCo_maybe :: Coercion -> Maybe (Coercion, Coercion)
-- ^ Attempt to take a coercion application apart.
splitAppCo_maybe (AppCo co1 co2) = Just (co1, co2)
splitAppCo_maybe (TyConAppCo tc cos)
  | isDecomposableTyCon tc || cos `lengthExceeds` tyConArity tc 
  , Just (cos', co') <- snocView cos
  = Just (mkTyConAppCo tc cos', co')    -- Never create unsaturated type family apps!
       -- Use mkTyConAppCo to preserve the invariant
       --  that identity coercions are always represented by Refl
splitAppCo_maybe (Refl ty) 
  | Just (ty1, ty2) <- splitAppTy_maybe ty 
  = Just (Refl ty1, Refl ty2)
splitAppCo_maybe _ = Nothing

splitForAllCo_maybe :: Coercion -> Maybe (TyVar, Coercion)
splitForAllCo_maybe (ForAllCo tv co) = Just (tv, co)
splitForAllCo_maybe _                = Nothing

-------------------------------------------------------
-- and some coercion kind stuff

coVarTypes :: CoVar -> (Type,Type) 
coVarTypes cv
 | Just (tc, [_k1,_k2,ty1,ty2]) <- splitTyConApp_maybe (varType cv)
 = ASSERT (tc `hasKey` eqPrimTyConKey)
   (ty1,ty2)
 | otherwise = panic "coVarTypes, non coercion variable"

coVarKind :: CoVar -> Type
coVarKind cv
  = ASSERT( isCoVar cv )
    varType cv

-- | Makes a coercion type from two types: the types whose equality 
-- is proven by the relevant 'Coercion'
mkCoercionType :: Type -> Type -> Type
mkCoercionType = mkPrimEqPred

isReflCo :: Coercion -> Bool
isReflCo (Refl {}) = True
isReflCo _         = False

isReflCo_maybe :: Coercion -> Maybe Type
isReflCo_maybe (Refl ty) = Just ty
isReflCo_maybe _         = Nothing
\end{code}

%************************************************************************
%*									*
            Building coercions
%*									*
%************************************************************************

\begin{code}
mkCoVarCo :: CoVar -> Coercion
-- cv :: s ~# t
mkCoVarCo cv
  | ty1 `eqType` ty2 = Refl ty1
  | otherwise        = CoVarCo cv
  where
    (ty1, ty2) = coVarTypes cv

mkReflCo :: Type -> Coercion
mkReflCo = Refl

mkAxInstCo :: CoAxiom br -> Int -> [Type] -> Coercion
-- mkAxInstCo can legitimately be called over-staturated; 
-- i.e. with more type arguments than the coercion requires
mkAxInstCo ax index tys
  | arity == n_tys = AxiomInstCo ax_br index rtys
  | otherwise      = ASSERT( arity < n_tys )
                     foldl AppCo (AxiomInstCo ax_br index (take arity rtys))
                                 (drop arity rtys)
  where
    n_tys = length tys
    arity = coAxiomArity ax index
    rtys  = map Refl tys
    ax_br = toBranchedAxiom ax

-- to be used only with singleton axioms (axioms with only one branch)
mkSingletonAxInstCo :: CoAxiom Unbranched -> [Type] -> Coercion
mkSingletonAxInstCo ax tys
  = mkAxInstCo ax 0 tys

mkAxInstRHS :: CoAxiom br -> Int -> [Type] -> Type
-- Instantiate the axiom with specified types,
-- returning the instantiated RHS
-- A companion to mkAxInstCo: 
--    mkAxInstRhs ax index tys = snd (coercionKind (mkAxInstCo ax index tys))
mkAxInstRHS ax index tys
  = ASSERT( tvs `equalLength` tys1 ) 
    mkAppTys rhs' tys2
  where
    branch       = coAxiomNthBranch ax index
    tvs          = coAxBranchTyVars branch
    (tys1, tys2) = splitAtList tvs tys
    rhs'         = substTyWith tvs tys1 (coAxBranchRHS branch)

mkSingletonAxInstRHS :: CoAxiom Unbranched -> [Type] -> Type
mkSingletonAxInstRHS ax = mkAxInstRHS ax 0

-- | Apply a 'Coercion' to another 'Coercion'.
mkAppCo :: Coercion -> Coercion -> Coercion
mkAppCo (Refl ty1) (Refl ty2)       = Refl (mkAppTy ty1 ty2)
mkAppCo (Refl (TyConApp tc tys)) co = TyConAppCo tc (map Refl tys ++ [co])
mkAppCo (TyConAppCo tc cos) co      = TyConAppCo tc (cos ++ [co])
mkAppCo co1 co2                     = AppCo co1 co2
-- Note, mkAppCo is careful to maintain invariants regarding
-- where Refl constructors appear; see the comments in the definition
-- of Coercion and the Note [Refl invariant] in types/TypeRep.lhs.

-- | Applies multiple 'Coercion's to another 'Coercion', from left to right.
-- See also 'mkAppCo'
mkAppCos :: Coercion -> [Coercion] -> Coercion
mkAppCos co1 tys = foldl mkAppCo co1 tys

-- | Apply a type constructor to a list of coercions.
mkTyConAppCo :: TyCon -> [Coercion] -> Coercion
mkTyConAppCo tc cos
	       -- Expand type synonyms
  | Just (tv_co_prs, rhs_ty, leftover_cos) <- tcExpandTyCon_maybe tc cos
  = mkAppCos (liftCoSubst tv_co_prs rhs_ty) leftover_cos

  | Just tys <- traverse isReflCo_maybe cos 
  = Refl (mkTyConApp tc tys)	-- See Note [Refl invariant]

  | otherwise = TyConAppCo tc cos

-- | Make a function 'Coercion' between two other 'Coercion's
mkFunCo :: Coercion -> Coercion -> Coercion
mkFunCo co1 co2 = mkTyConAppCo funTyCon [co1, co2]

-- | Make a 'Coercion' which binds a variable within an inner 'Coercion'
mkForAllCo :: Var -> Coercion -> Coercion
-- note that a TyVar should be used here, not a CoVar (nor a TcTyVar)
mkForAllCo tv (Refl ty) = ASSERT( isTyVar tv ) Refl (mkForAllTy tv ty)
mkForAllCo tv  co       = ASSERT ( isTyVar tv ) ForAllCo tv co

-------------------------------

-- | Create a symmetric version of the given 'Coercion' that asserts
--   equality between the same types but in the other "direction", so
--   a kind of @t1 ~ t2@ becomes the kind @t2 ~ t1@.
mkSymCo :: Coercion -> Coercion

-- Do a few simple optimizations, but don't bother pushing occurrences
-- of symmetry to the leaves; the optimizer will take care of that.
mkSymCo co@(Refl {})              = co
mkSymCo    (UnsafeCo ty1 ty2)    = UnsafeCo ty2 ty1
mkSymCo    (SymCo co)            = co
mkSymCo co                       = SymCo co

-- | Create a new 'Coercion' by composing the two given 'Coercion's transitively.
mkTransCo :: Coercion -> Coercion -> Coercion
mkTransCo (Refl _) co = co
mkTransCo co (Refl _) = co
mkTransCo co1 co2     = TransCo co1 co2

mkNthCo :: Int -> Coercion -> Coercion
mkNthCo n (Refl ty) = ASSERT( ok_tc_app ty n ) 
                      Refl (tyConAppArgN n ty)
mkNthCo n co        = ASSERT( ok_tc_app _ty1 n && ok_tc_app _ty2 n )
                      NthCo n co
                    where
                      Pair _ty1 _ty2 = coercionKind co

mkLRCo :: LeftOrRight -> Coercion -> Coercion
mkLRCo lr (Refl ty) = Refl (pickLR lr (splitAppTy ty))
mkLRCo lr co        = LRCo lr co

ok_tc_app :: Type -> Int -> Bool
ok_tc_app ty n = case splitTyConApp_maybe ty of
                   Just (_, tys) -> tys `lengthExceeds` n
                   Nothing       -> False

-- | Instantiates a 'Coercion' with a 'Type' argument. 
mkInstCo :: Coercion -> Type -> Coercion
mkInstCo co ty = InstCo co ty

-- | Manufacture a coercion from thin air. Needless to say, this is
--   not usually safe, but it is used when we know we are dealing with
--   bottom, which is one case in which it is safe.  This is also used
--   to implement the @unsafeCoerce#@ primitive.  Optimise by pushing
--   down through type constructors.
mkUnsafeCo :: Type -> Type -> Coercion
mkUnsafeCo ty1 ty2 | ty1 `eqType` ty2 = Refl ty1
mkUnsafeCo (TyConApp tc1 tys1) (TyConApp tc2 tys2)
  | tc1 == tc2
  = mkTyConAppCo tc1 (zipWith mkUnsafeCo tys1 tys2)

mkUnsafeCo (FunTy a1 r1) (FunTy a2 r2)
  = mkFunCo (mkUnsafeCo a1 a2) (mkUnsafeCo r1 r2)

mkUnsafeCo ty1 ty2 = UnsafeCo ty1 ty2

-- See note [Newtype coercions] in TyCon

-- | Create a coercion constructor (axiom) suitable for the given
--   newtype 'TyCon'. The 'Name' should be that of a new coercion
--   'CoAxiom', the 'TyVar's the arguments expected by the @newtype@ and
--   the type the appropriate right hand side of the @newtype@, with
--   the free variables a subset of those 'TyVar's.
mkNewTypeCo :: Name -> TyCon -> [TyVar] -> Type -> CoAxiom Unbranched
mkNewTypeCo name tycon tvs rhs_ty
  = CoAxiom { co_ax_unique   = nameUnique name
            , co_ax_name     = name
            , co_ax_implicit = True  -- See Note [Implicit axioms] in TyCon
            , co_ax_tc       = tycon
            , co_ax_branches = FirstBranch branch }
  where branch = CoAxBranch { cab_tvs = tvs
                            , cab_lhs = mkTyCoVarTys tvs
                            , cab_rhs = rhs_ty }

mkPiCos :: [Var] -> Coercion -> Coercion
mkPiCos vs co = foldr mkPiCo co vs

mkPiCo  :: Var -> Coercion -> Coercion
mkPiCo v co | isTyVar v = mkForAllCo v co
            | otherwise = mkFunCo (mkReflCo (varType v)) co

mkCoCast :: Coercion -> Coercion -> Coercion
-- (mkCoCast (c :: s1 ~# t1) (g :: (s1 ~# t1) ~# (s2 ~# t2)
mkCoCast c g
  = mkSymCo g1 `mkTransCo` c `mkTransCo` g2
  where
       -- g  :: (s1 ~# s2) ~# (t1 ~#  t2)
       -- g1 :: s1 ~# t1
       -- g2 :: s2 ~# t2
    [_reflk, g1, g2] = decomposeCo 3 g
            -- Remember, (~#) :: forall k. k -> k -> *
            -- so it takes *three* arguments, not two
\end{code}

%************************************************************************
%*									*
            Newtypes
%*									*
%************************************************************************

\begin{code}
instNewTyCon_maybe :: TyCon -> [Type] -> Maybe (Type, Coercion)
-- ^ If @co :: T ts ~ rep_ty@ then:
--
-- > instNewTyCon_maybe T ts = Just (rep_ty, co)
instNewTyCon_maybe tc tys
  | Just (tvs, ty, co_tc) <- unwrapNewTyCon_maybe tc
  = ASSERT( tys `lengthIs` tyConArity tc )
    Just (substTyWith tvs tys ty, mkSingletonAxInstCo co_tc tys)
  | otherwise
  = Nothing

-- this is here to avoid module loops
splitNewTypeRepCo_maybe :: Type -> Maybe (Type, Coercion)  
-- ^ Sometimes we want to look through a @newtype@ and get its associated coercion.
-- This function only strips *one layer* of @newtype@ off, so the caller will usually call
-- itself recursively. Furthermore, this function should only be applied to types of kind @*@,
-- hence the newtype is always saturated. If @co : ty ~ ty'@ then:
--
-- > splitNewTypeRepCo_maybe ty = Just (ty', co)
--
-- The function returns @Nothing@ for non-@newtypes@ or fully-transparent @newtype@s.
splitNewTypeRepCo_maybe ty 
  | Just ty' <- coreView ty = splitNewTypeRepCo_maybe ty'
splitNewTypeRepCo_maybe (TyConApp tc tys)
  | Just (ty', co) <- instNewTyCon_maybe tc tys
  = case co of
	Refl _ -> panic "splitNewTypeRepCo_maybe"
			-- This case handled by coreView
	_      -> Just (ty', co)
splitNewTypeRepCo_maybe _
  = Nothing

-- | Determines syntactic equality of coercions
coreEqCoercion :: Coercion -> Coercion -> Bool
coreEqCoercion co1 co2 = coreEqCoercion2 rn_env co1 co2
  where rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfCo co1 `unionVarSet` tyCoVarsOfCo co2))

coreEqCoercion2 :: RnEnv2 -> Coercion -> Coercion -> Bool
coreEqCoercion2 env (Refl ty1) (Refl ty2) = eqTypeX env ty1 ty2
coreEqCoercion2 env (TyConAppCo tc1 cos1) (TyConAppCo tc2 cos2)
  = tc1 == tc2 && all2 (coreEqCoercion2 env) cos1 cos2

coreEqCoercion2 env (AppCo co11 co12) (AppCo co21 co22)
  = coreEqCoercion2 env co11 co21 && coreEqCoercion2 env co12 co22

coreEqCoercion2 env (ForAllCo v1 co1) (ForAllCo v2 co2)
  = coreEqCoercion2 (rnBndr2 env v1 v2) co1 co2

coreEqCoercion2 env (CoVarCo cv1) (CoVarCo cv2)
  = rnOccL env cv1 == rnOccR env cv2

coreEqCoercion2 env (AxiomInstCo con1 ind1 cos1) (AxiomInstCo con2 ind2 cos2)
  = con1 == con2
    && ind1 == ind2
    && all2 (coreEqCoercion2 env) cos1 cos2

coreEqCoercion2 env (UnsafeCo ty11 ty12) (UnsafeCo ty21 ty22)
  = eqTypeX env ty11 ty21 && eqTypeX env ty12 ty22

coreEqCoercion2 env (SymCo co1) (SymCo co2)
  = coreEqCoercion2 env co1 co2

coreEqCoercion2 env (TransCo co11 co12) (TransCo co21 co22)
  = coreEqCoercion2 env co11 co21 && coreEqCoercion2 env co12 co22

coreEqCoercion2 env (NthCo d1 co1) (NthCo d2 co2)
  = d1 == d2 && coreEqCoercion2 env co1 co2
coreEqCoercion2 env (LRCo d1 co1) (LRCo d2 co2)
  = d1 == d2 && coreEqCoercion2 env co1 co2

coreEqCoercion2 env (InstCo co1 ty1) (InstCo co2 ty2)
  = coreEqCoercion2 env co1 co2 && eqTypeX env ty1 ty2

coreEqCoercion2 _ _ _ = False
\end{code}

%************************************************************************
%*									*
                   Substitution of coercions
%*                                                                      *
%************************************************************************

\begin{code}

substCoWithTy :: InScopeSet -> TyVar -> Type -> Coercion -> Coercion
substCoWithTy in_scope tv ty = substCoWithTys in_scope [tv] [ty]

substCoWithTys :: InScopeSet -> [TyVar] -> [Type] -> Coercion -> Coercion
substCoWithTys in_scope tvs tys co
  | debugIsOn && (length tvs /= length tys)
  = pprTrace "substCoWithTys" (ppr tvs $$ ppr tys) co
  | otherwise 
  = ASSERT( length tvs == length tys )
    substCo (TCvSubst in_scope (zipVarEnv tvs tys) emptyVarEnv) co

\end{code}

%************************************************************************
%*									*
                   "Lifting" substitution
	   [(TyVar,Coercion)] -> Type -> Coercion
%*                                                                      *
%************************************************************************

\begin{code}
data LiftCoSubst = LCS InScopeSet LiftCoEnv

type LiftCoEnv = VarEnv Coercion
     -- Maps *type variables* to *coercions*
     -- That's the whole point of this function!

liftCoSubstWith :: [TyVar] -> [Coercion] -> Type -> Coercion
liftCoSubstWith tvs cos ty
  = liftCoSubst (zipEqual "liftCoSubstWith" tvs cos) ty

liftCoSubst :: [(TyVar,Coercion)] -> Type -> Coercion
liftCoSubst prs ty
 | null prs  = Refl ty
 | otherwise = ty_co_subst (LCS (mkInScopeSet (tyCoVarsOfCos (map snd prs)))
                                (mkVarEnv prs)) ty

-- | The \"lifting\" operation which substitutes coercions for type
--   variables in a type to produce a coercion.
--
--   For the inverse operation, see 'liftCoMatch' 
ty_co_subst :: LiftCoSubst -> Type -> Coercion
ty_co_subst subst ty
  = go ty
  where
    go (TyVarTy tv)      = liftCoSubstTyVar subst tv `orElse` Refl (TyVarTy tv)
       			     -- A type variable from a non-cloned forall
			     -- won't be in the substitution
    go (AppTy ty1 ty2)   = mkAppCo (go ty1) (go ty2)
    go (TyConApp tc tys) = mkTyConAppCo tc (map go tys)
                           -- IA0_NOTE: Do we need to do anything
                           -- about kind instantiations? I don't think
                           -- so.  see Note [Kind coercions]
    go (FunTy ty1 ty2)   = mkFunCo (go ty1) (go ty2)
    go (ForAllTy v ty)   = mkForAllCo v' $! (ty_co_subst subst' ty)
                         where
                           (subst', v') = liftCoSubstTyVarBndr subst v
    go ty@(LitTy {})     = mkReflCo ty

liftCoSubstTyVar :: LiftCoSubst -> TyVar -> Maybe Coercion
liftCoSubstTyVar (LCS _ cenv) tv = lookupVarEnv cenv tv 

liftCoSubstTyVarBndr :: LiftCoSubst -> TyVar -> (LiftCoSubst, TyVar)
liftCoSubstTyVarBndr (LCS in_scope cenv) old_var
  = (LCS (in_scope `extendInScopeSet` new_var) new_cenv, new_var)		
  where
    new_cenv | no_change = delVarEnv cenv old_var
	     | otherwise = extendVarEnv cenv old_var (Refl (TyVarTy new_var))

    no_change = new_var == old_var
    new_var = uniqAway in_scope old_var
\end{code}

\begin{code}
-- | 'liftCoMatch' is sort of inverse to 'liftCoSubst'.  In particular, if
--   @liftCoMatch vars ty co == Just s@, then @tyCoSubst s ty == co@.
--   That is, it matches a type against a coercion of the same
--   "shape", and returns a lifting substitution which could have been
--   used to produce the given coercion from the given type.
liftCoMatch :: TyVarSet -> Type -> Coercion -> Maybe LiftCoSubst
liftCoMatch tmpls ty co 
  = case ty_co_match menv emptyVarEnv ty co of
      Just cenv -> Just (LCS in_scope cenv)
      Nothing   -> Nothing
  where
    menv     = ME { me_tmpls = tmpls, me_env = mkRnEnv2 in_scope }
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOfCo co)
    -- Like tcMatchTy, assume all the interesting variables 
    -- in ty are in tmpls

-- | 'ty_co_match' does all the actual work for 'liftCoMatch'.
ty_co_match :: MatchEnv -> LiftCoEnv -> Type -> Coercion -> Maybe LiftCoEnv
ty_co_match menv subst ty co 
  | Just ty' <- coreView ty = ty_co_match menv subst ty' co

  -- Match a type variable against a non-refl coercion
ty_co_match menv cenv (TyVarTy tv1) co
  | Just co1' <- lookupVarEnv cenv tv1'      -- tv1' is already bound to co1
  = if coreEqCoercion2 (nukeRnEnvL rn_env) co1' co
    then Just cenv
    else Nothing       -- no match since tv1 matches two different coercions

  | tv1' `elemVarSet` me_tmpls menv           -- tv1' is a template var
  = if any (inRnEnvR rn_env) (varSetElems (tyCoVarsOfCo co))
    then Nothing      -- occurs check failed
    else return (extendVarEnv cenv tv1' co)
        -- BAY: I don't think we need to do any kind matching here yet
        -- (compare 'match'), but we probably will when moving to SHE.

  | otherwise    -- tv1 is not a template ty var, so the only thing it
                 -- can match is a reflexivity coercion for itself.
		 -- But that case is dealt with already
  = Nothing

  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1

ty_co_match menv subst (AppTy ty1 ty2) co
  | Just (co1, co2) <- splitAppCo_maybe co	-- c.f. Unify.match on AppTy
  = do { subst' <- ty_co_match menv subst ty1 co1 
       ; ty_co_match menv subst' ty2 co2 }

ty_co_match menv subst (TyConApp tc1 tys) (TyConAppCo tc2 cos)
  | tc1 == tc2 = ty_co_matches menv subst tys cos

ty_co_match menv subst (FunTy ty1 ty2) (TyConAppCo tc cos)
  | tc == funTyCon = ty_co_matches menv subst [ty1,ty2] cos

ty_co_match menv subst (ForAllTy tv1 ty) (ForAllCo tv2 co) 
  = ty_co_match menv' subst ty co
  where
    menv' = menv { me_env = rnBndr2 (me_env menv) tv1 tv2 }

ty_co_match menv subst ty co
  | Just co' <- pushRefl co = ty_co_match menv subst ty co'
  | otherwise               = Nothing

ty_co_matches :: MatchEnv -> LiftCoEnv -> [Type] -> [Coercion] -> Maybe LiftCoEnv
ty_co_matches menv = matchList (ty_co_match menv)

pushRefl :: Coercion -> Maybe Coercion
pushRefl (Refl (AppTy ty1 ty2))   = Just (AppCo (Refl ty1) (Refl ty2))
pushRefl (Refl (FunTy ty1 ty2))   = Just (TyConAppCo funTyCon [Refl ty1, Refl ty2])
pushRefl (Refl (TyConApp tc tys)) = Just (TyConAppCo tc (map Refl tys))
pushRefl (Refl (ForAllTy tv ty))  = Just (ForAllCo tv (Refl ty))
pushRefl _                        = Nothing
\end{code}

%************************************************************************
%*									*
            Sequencing on coercions
%*									*
%************************************************************************

\begin{code}
seqCo :: Coercion -> ()
seqCo (Refl ty)             = seqType ty
seqCo (TyConAppCo tc cos)   = tc `seq` seqCos cos
seqCo (AppCo co1 co2)       = seqCo co1 `seq` seqCo co2
seqCo (ForAllCo tv co)      = tv `seq` seqCo co
seqCo (CoVarCo cv)          = cv `seq` ()
seqCo (AxiomInstCo con ind cos) = con `seq` ind `seq` seqCos cos
seqCo (UnsafeCo ty1 ty2)    = seqType ty1 `seq` seqType ty2
seqCo (SymCo co)            = seqCo co
seqCo (TransCo co1 co2)     = seqCo co1 `seq` seqCo co2
seqCo (NthCo _ co)          = seqCo co
seqCo (LRCo _ co)           = seqCo co
seqCo (InstCo co ty)        = seqCo co `seq` seqType ty

seqCos :: [Coercion] -> ()
seqCos []       = ()
seqCos (co:cos) = seqCo co `seq` seqCos cos
\end{code}


%************************************************************************
%*									*
	     The kind of a type, and of a coercion
%*									*
%************************************************************************

\begin{code}
coercionType :: Coercion -> Type
coercionType co = case coercionKind co of
                    Pair ty1 ty2 -> mkCoercionType ty1 ty2

------------------
-- | If it is the case that
--
-- > c :: (t1 ~ t2)
--
-- i.e. the kind of @c@ relates @t1@ and @t2@, then @coercionKind c = Pair t1 t2@.

coercionKind :: Coercion -> Pair Type 
coercionKind co = go co
  where 
    go (Refl ty)            = Pair ty ty
    go (TyConAppCo tc cos)  = mkTyConApp tc <$> (sequenceA $ map go cos)
    go (AppCo co1 co2)      = mkAppTy <$> go co1 <*> go co2
    go (ForAllCo tv co)     = mkForAllTy tv <$> go co
    go (CoVarCo cv)         = toPair $ coVarTypes cv
    go (AxiomInstCo ax ind cos)
      = let branch         = coAxiomNthBranch ax ind
            tvs            = coAxBranchTyVars branch
            Pair tys1 tys2 = sequenceA $ map go cos 
        in  Pair (substTyWith tvs tys1 (coAxNthLHS ax ind))
                 (substTyWith tvs tys2 (coAxBranchRHS branch))
    go (UnsafeCo ty1 ty2)   = Pair ty1 ty2
    go (SymCo co)           = swap $ go co
    go (TransCo co1 co2)    = Pair (pFst $ go co1) (pSnd $ go co2)
    go (NthCo d co)         = tyConAppArgN d <$> go co
    go (LRCo lr co)         = (pickLR lr . splitAppTy) <$> go co
    go (InstCo aco ty)      = go_app aco [ty]

    go_app :: Coercion -> [Type] -> Pair Type
    -- Collect up all the arguments and apply all at once
    -- See Note [Nested InstCos]
    go_app (InstCo co ty) tys = go_app co (ty:tys)
    go_app co             tys = (`applyTys` tys) <$> go co

-- | Apply 'coercionKind' to multiple 'Coercion's
coercionKinds :: [Coercion] -> Pair [Type]
coercionKinds tys = sequenceA $ map coercionKind tys
\end{code}

Note [Nested InstCos]
~~~~~~~~~~~~~~~~~~~~~
In Trac #5631 we found that 70% of the entire compilation time was
being spent in coercionKind!  The reason was that we had
   (g @ ty1 @ ty2 .. @ ty100)    -- The "@s" are InstCos
where 
   g :: forall a1 a2 .. a100. phi
If we deal with the InstCos one at a time, we'll do this:
   1.  Find the kind of (g @ ty1 .. @ ty99) : forall a100. phi'
   2.  Substitute phi'[ ty100/a100 ], a single tyvar->type subst
But this is a *quadratic* algorithm, and the blew up Trac #5631.
So it's very important to do the substitution simultaneously.

cf Type.applyTys (which in fact we call here)


\begin{code}
applyCo :: Type -> Coercion -> Type
-- Gives the type of (e co) where e :: (a~b) => ty
applyCo ty co | Just ty' <- coreView ty = applyCo ty' co
applyCo (FunTy _ ty) _ = ty
applyCo _            _ = panic "applyCo"
\end{code}

Note [Kind coercions]
~~~~~~~~~~~~~~~~~~~~~
Kind coercions are only of the form: Refl kind. They are only used to
instantiate kind polymorphic type constructors in TyConAppCo. Remember
that kind instantiation only happens with TyConApp, not AppTy.
