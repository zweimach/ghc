%
% (c) The University of Glasgow 2006
%

\begin{code}
{-# LANGUAGE RankNTypes #-}
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
        mkAxInstCo, mkUnbranchedAxInstCo, mkAxInstLHS, mkAxInstRHS,
        mkUnbranchedAxInstRHS,
        mkPiCo, mkPiCos, mkCoCast,
        mkSymCo, mkTransCo, mkNthCo, mkLRCo,
	mkInstCo, mkAppCo, mkTyConAppCo, mkFunCo,
        mkForAllCo, mkForAllCo_TyHomo, mkForAllCo_CoHomo,
        mkUnsafeCo, mkNewTypeCo, 

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
	cvTvSubst, tvCvSubst, mkCvSubst, zipOpenCvSubst,
        substTy, extendTvSubst, extendCvSubstAndInScope,
	substCoVarBndr,

	-- ** Lifting
	liftCoMatch, liftCoSubstTyVar, liftCoSubstWith, liftCoSubstWithEx,
        
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
import Name	( Name, NamedThing(..), nameUnique, getSrcSpan )
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
            Coercions
%*									*
%************************************************************************

\begin{code}
-- | A 'Coercion' is concrete evidence of the equality/convertibility
-- of two types.

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data Coercion 
  -- These ones mirror the shape of types
  = Refl Type  -- See Note [Refl invariant]
          -- Invariant: applications of (Refl T) to a bunch of identity coercions
          --            always show up as Refl.
          -- For example  (Refl T) (Refl a) (Refl b) shows up as (Refl (T a b)).

          -- Applications of (Refl T) to some coercions, at least one of
          -- which is NOT the identity, show up as TyConAppCo.
          -- (They may not be fully saturated however.)
          -- ConAppCo coercions (like all coercions other than Refl)
          -- are NEVER the identity.

  -- These ones simply lift the correspondingly-named 
  -- Type constructors into Coercions
  | TyConAppCo TyCon [Coercion]    -- lift TyConApp 
    	       -- The TyCon is never a synonym; 
	       -- we expand synonyms eagerly
	       -- But it can be a type function

  | AppCo Coercion Coercion        -- lift AppTy

  -- See Note [Forall coercions]
  | ForAllCo TyVar Coercion       -- forall a. g

  -- These are special
  | CoVarCo CoVar
  | AxiomInstCo (CoAxiom Branched) Int [Coercion]
     -- The coercion arguments always *precisely* saturate arity of CoAxiom.
     -- See [Coercion axioms applied to coercions]
     -- See also [CoAxiom index]
  | UnsafeCo Type Type
  | SymCo Coercion
  | TransCo Coercion Coercion

  -- These are destructors
  | NthCo  Int         Coercion     -- Zero-indexed; decomposes (T t0 ... tn)
  | LRCo   LeftOrRight Coercion     -- Decomposes (t_left t_right)
  | InstCo Coercion Type
  deriving (Data.Data, Data.Typeable)

-- If you edit this type, you may need to update the GHC formalism
-- See Note [GHC Formalism] in coreSyn/CoreLint.lhs
data LeftOrRight = CLeft | CRight 
                 deriving( Eq, Data.Data, Data.Typeable )

pickLR :: LeftOrRight -> (a,a) -> a
pickLR CLeft  (l,_) = l
pickLR CRight (_,r) = r
\end{code}


Note [Refl invariant]
~~~~~~~~~~~~~~~~~~~~~
Coercions have the following invariant 
     Refl is always lifted as far as possible.  

You might think that a consequencs is:
     Every identity coercions has Refl at the root

But that's not quite true because of coercion variables.  Consider
     g         where g :: Int~Int
     Left h    where h :: Maybe Int ~ Maybe Int
etc.  So the consequence is only true of coercions that
have no coercion variables.

Note [Coercion axioms applied to coercions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The reason coercion axioms can be applied to coercions and not just
types is to allow for better optimization.  There are some cases where
we need to be able to "push transitivity inside" an axiom in order to
expose further opportunities for optimization.  

For example, suppose we have

  C a : t[a] ~ F a
  g   : b ~ c

and we want to optimize

  sym (C b) ; t[g] ; C c

which has the kind

  F b ~ F c

(stopping through t[b] and t[c] along the way).

We'd like to optimize this to just F g -- but how?  The key is
that we need to allow axioms to be instantiated by *coercions*,
not just by types.  Then we can (in certain cases) push
transitivity inside the axiom instantiations, and then react
opposite-polarity instantiations of the same axiom.  In this
case, e.g., we match t[g] against the LHS of (C c)'s kind, to
obtain the substitution  a |-> g  (note this operation is sort
of the dual of lifting!) and hence end up with

  C g : t[b] ~ F c

which indeed has the same kind as  t[g] ; C c.

Now we have

  sym (C b) ; C g

which can be optimized to F g.

Note [CoAxiom index]
~~~~~~~~~~~~~~~~~~~~
A CoAxiom has 1 or more branches. Each branch has contains a list
of the free type variables in that branch, the LHS type patterns,
and the RHS type for that branch. When we apply an axiom to a list
of coercions, we must choose which branch of the axiom we wish to
use, as the different branches may have different numbers of free
type variables. (The number of type patterns is always the same
among branches, but that doesn't quite concern us here.)

The Int in the AxiomInstCo constructor is the 0-indexed number
of the chosen branch.

Note [Forall coercions]
~~~~~~~~~~~~~~~~~~~~~~~
Constructing coercions between forall-types can be a bit tricky.
Currently, the situation is as follows:

  ForAllCo TyVar Coercion

represents a coercion between polymorphic types, with the rule

           v : k       g : t1 ~ t2
  ----------------------------------------------
  ForAllCo v g : (all v:k . t1) ~ (all v:k . t2)

Note that it's only necessary to coerce between polymorphic types
where the type variables have identical kinds, because equality on
kinds is trivial.

Note [Predicate coercions]
~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have
   g :: a~b
How can we coerce between types
   ([c]~a) => [a] -> c
and
   ([c]~b) => [b] -> c
where the equality predicate *itself* differs?

Answer: we simply treat (~) as an ordinary type constructor, so these
types really look like

   ((~) [c] a) -> [a] -> c
   ((~) [c] b) -> [b] -> c

So the coercion between the two is obviously

   ((~) [c] g) -> [g] -> c

Another way to see this to say that we simply collapse predicates to
their representation type (see Type.coreView and Type.predTypeRep).

This collapse is done by mkPredCo; there is no PredCo constructor
in Coercion.  This is important because we need Nth to work on 
predicates too:
    Nth 1 ((~) [c] g) = g
See Simplify.simplCoercionF, which generates such selections.

Note [Kind coercions]
~~~~~~~~~~~~~~~~~~~~~
Suppose T :: * -> *, and g :: A ~ B
Then the coercion
   TyConAppCo T [g]      T g : T A ~ T B

Now suppose S :: forall k. k -> *, and g :: A ~ B
Then the coercion
   TyConAppCo S [Refl *, g]   T <*> g : T * A ~ T * B

Notice that the arguments to TyConAppCo are coercions, but the first
represents a *kind* coercion. Now, we don't allow any non-trivial kind
coercions, so it's an invariant that any such kind coercions are Refl.
Lint checks this. 

However it's inconvenient to insist that these kind coercions are always
*structurally* (Refl k), because the key function exprIsConApp_maybe
pushes coercions into constructor arguments, so 
       C k ty e |> g
may turn into
       C (Nth 0 g) ....
Now (Nth 0 g) will optimise to Refl, but perhaps not instantly.

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
tyCoVarsOfCo :: Coercion -> VarSet
-- Extracts type and coercion variables from a coercion
tyCoVarsOfCo (Refl ty)           = tyVarsOfType ty
tyCoVarsOfCo (TyConAppCo _ cos)  = tyCoVarsOfCos cos
tyCoVarsOfCo (AppCo co1 co2)     = tyCoVarsOfCo co1 `unionVarSet` tyCoVarsOfCo co2
tyCoVarsOfCo (ForAllCo tv co)    = tyCoVarsOfCo co `delVarSet` tv
tyCoVarsOfCo (CoVarCo v)         = unitVarSet v
tyCoVarsOfCo (AxiomInstCo _ _ cos) = tyCoVarsOfCos cos
tyCoVarsOfCo (UnsafeCo ty1 ty2)  = tyVarsOfType ty1 `unionVarSet` tyVarsOfType ty2
tyCoVarsOfCo (SymCo co)          = tyCoVarsOfCo co
tyCoVarsOfCo (TransCo co1 co2)   = tyCoVarsOfCo co1 `unionVarSet` tyCoVarsOfCo co2
tyCoVarsOfCo (NthCo _ co)        = tyCoVarsOfCo co
tyCoVarsOfCo (LRCo _ co)         = tyCoVarsOfCo co
tyCoVarsOfCo (InstCo co ty)      = tyCoVarsOfCo co `unionVarSet` tyVarsOfType ty

tyCoVarsOfCos :: [Coercion] -> VarSet
tyCoVarsOfCos cos = foldr (unionVarSet . tyCoVarsOfCo) emptyVarSet cos

coVarsOfCo :: Coercion -> VarSet
-- Extract *coerction* variables only.  Tiresome to repeat the code, but easy.
coVarsOfCo (Refl _)            = emptyVarSet
coVarsOfCo (TyConAppCo _ cos)  = coVarsOfCos cos
coVarsOfCo (AppCo co1 co2)     = coVarsOfCo co1 `unionVarSet` coVarsOfCo co2
coVarsOfCo (ForAllCo _ co)     = coVarsOfCo co
coVarsOfCo (CoVarCo v)         = unitVarSet v
coVarsOfCo (AxiomInstCo _ _ cos) = coVarsOfCos cos
coVarsOfCo (UnsafeCo _ _)      = emptyVarSet
coVarsOfCo (SymCo co)          = coVarsOfCo co
coVarsOfCo (TransCo co1 co2)   = coVarsOfCo co1 `unionVarSet` coVarsOfCo co2
coVarsOfCo (NthCo _ co)        = coVarsOfCo co
coVarsOfCo (LRCo _ co)         = coVarsOfCo co
coVarsOfCo (InstCo co _)       = coVarsOfCo co

coVarsOfCos :: [Coercion] -> VarSet
coVarsOfCos cos = foldr (unionVarSet . coVarsOfCo) emptyVarSet cos

coercionSize :: Coercion -> Int
coercionSize (Refl ty)           = typeSize ty
coercionSize (TyConAppCo _ args) = 1 + sum (map coercionArgSize args)
coercionSize (AppCo co arg)      = coercionSize co + coercionArgSize arg
coercionSize (ForAllCo _ co)     = 1 + coercionSize co
coercionSize (CoVarCo _)         = 1
coercionSize (AxiomInstCo _ _ args) = 1 + sum (map coercionArgSize args)
coercionSize (UnsafeCo ty1 ty2)  = typeSize ty1 + typeSize ty2
coercionSize (SymCo co)          = 1 + coercionSize co
coercionSize (TransCo co1 co2)   = 1 + coercionSize co1 + coercionSize co2
coercionSize (NthCo _ co)        = 1 + coercionSize co
coercionSize (LRCo  _ co)        = 1 + coercionSize co
coercionSize (InstCo co arg)     = 1 + coercionSize co + coercionArgSize arg
coercionSize (CoherenceCo c1 c2) = 1 + coercionSize c1 + coercionSize c2
coercionSize (KindCo co)         = 1 + coercionSize co

coercionArgSize :: CoercionArg -> Int
coercionArgSize (TyCoArg co)     = coercionSize co
coercionArgSize (CoCoArg c1 c2)  = coercionSize c1 + coercionSize c2
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

ppr_co p (TyConAppCo tc args)  = pprTcApp   p ppr_co tc args
ppr_co p (AppCo co arg)        = maybeParen p TyConPrec $
                                 pprCo co <+> ppr_arg TyConPrec arg
ppr_co p co@(ForAllCo {})      = ppr_forall_co p co
ppr_co _ (CoVarCo cv)          = parenSymOcc (getOccName cv) (ppr cv)
ppr_co p (AxiomInstCo con index args)
  = angleBrackets (pprPrefixApp p 
                    (ppr (getName con) <> brackets (ppr index))
                    (map (ppr_arg TyConPrec) args))

ppr_co p co@(TransCo {}) = maybeParen p FunPrec $
                           case trans_co_list co [] of
                             [] -> panic "ppr_co"
                             (co:cos) -> sep ( ppr_co FunPrec co
                                             : [ char ';' <+> ppr_co FunPrec co | co <- cos])
ppr_co p (InstCo co arg) = maybeParen p TyConPrec $
                           pprParendCo co <> ptext (sLit "@") <> ppr_arg TopPrec arg

ppr_co p (UnsafeCo ty1 ty2)  = pprPrefixApp p (ptext (sLit "UnsafeCo")) 
                                           [pprParendType ty1, pprParendType ty2]
ppr_co p (SymCo co)          = pprPrefixApp p (ptext (sLit "Sym")) [pprParendCo co]
ppr_co p (NthCo n co)        = pprPrefixApp p (ptext (sLit "Nth:") <> int n) [pprParendCo co]
ppr_co p (LRCo sel co)       = pprPrefixApp p (ppr sel) [pprParendCo co]
ppr_co p (CoherenceCo c1 c2) = parens $
                               (ppr_co FunPrec c1) <+> (ptext (sLit "|>")) <+>
                               (ppr_co FunPrec c2)
ppr_co p (KindCo co)         = pprPrefixApp p (ptext (sLit "kind")) [pprParendCo co]

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
ppr_forall_co p (ForAllCo cobndr co)
  = maybeParen p FunPrec $
    sep [ppr_forall_cobndr cobndr, ppr_co TopPrec co]

ppr_forall_cobndr :: ForAllCoBndr -> SDoc
ppr_forall_cobndr cobndr = pprForAll (coBndrVars cobndr)
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
	Destructing coercions		
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
splitTyConAppCo_maybe :: Coercion -> Maybe (TyCon, [CoercionArg])
splitTyConAppCo_maybe (Refl ty)           = (fmap . second . map) liftSimply (splitTyConApp_maybe ty)
splitTyConAppCo_maybe (TyConAppCo tc cos) = Just (tc, cos)
splitTyConAppCo_maybe _                   = Nothing

splitAppCo_maybe :: Coercion -> Maybe (Coercion, CoercionArg)
-- ^ Attempt to take a coercion application apart.
splitAppCo_maybe (AppCo co arg) = Just (co, arg)
splitAppCo_maybe (TyConAppCo tc args)
  | isDecomposableTyCon tc || args `lengthExceeds` tyConArity tc 
  , Just (args', arg') <- snocView args
  = Just (mkTyConAppCo tc args', arg')    -- Never create unsaturated type family apps!
       -- Use mkTyConAppCo to preserve the invariant
       --  that identity coercions are always represented by Refl
splitAppCo_maybe (Refl ty) 
  | Just (ty1, ty2) <- splitAppTy_maybe ty 
  = Just (liftSimply ty1, liftSimply ty2)
splitAppCo_maybe _ = Nothing

splitForAllCo_maybe :: Coercion -> Maybe (ForAllCoBndr, Coercion)
splitForAllCo_maybe (ForAllCo cobndr co) = Just (cobndr, co)
splitForAllCo_maybe _                    = Nothing

-- returns the two type variables abstracted over
splitForAllCo_Ty_maybe :: Coercion -> Maybe (TyVar, TyVar, Coercion)
splitForAllCo_Ty_maybe (ForAllCo (TyHomo tv) co)            = Just (tv, tv, co)
splitForAllCo_Ty_maybe (ForAllCo (TyHetero _ tv1 tv2 _) co) = Just (tv1, tv2, co)
splitForAllCo_Ty_maybe _                                    = Nothing

-- returns the two coercion variables abstracted over
splitForAllCo_Co_maybe :: Coercion -> Maybe (CoVar, CoVar, Coercion)
splitForAllCo_Co_maybe (ForAllCo (CoHomo cv) co)          = Just (cv, cv, co)
splitForAllCo_Co_maybe (ForAllCo (CoHetero _ cv1 cv2) co) = Just (cv1, cv2, co)
splitForAllCo_Co_maybe _                                  = Nothing

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

-- | Returns the Refl'd type if the CoercionArg is "Refl-like".
-- A TyCoArg (Refl ...) is Refl-like.
-- A CoCoArg co1 co2 is Refl-like if co1 and co2 have the same type.
-- The Type returned in the second case is the first coercion in the CoCoArg.
isReflLike_maybe :: CoercionArg -> Maybe Type
isReflLike_maybe (TyCoArg (Refl ty)) = Just ty
isReflLike_maybe (CoCoArg co1 co2)
  | coercionType co1 `eqType` coercionType co2
  = Just $ CoercionTy co1

isReflLike_maybe _ = Nothing
\end{code}

%************************************************************************
%*									*
            Building coercions
%*									*
%************************************************************************

These "smart constructors" maintain the invariants listed in the definition
of Coercion, and they perform very basic optimizations. Note that if you
add a new optimization here, you will have to update the code in Unify
to account for it. These smart constructors are used in substitution, so
to preserve the semantics of matching and unification, those algorithms must
be aware of any optimizations done here.

See also Note [Coercion optimizations and match_co] in Unify.

Note [Don't optimize mkTransCo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
One would expect to implement the following two optimizations in mkTransCo:
  mkTransCo co1 (Refl ...) --> co1
  mkTransCo (Refl ...) co1 --> co1

However, doing this would make unification require backtracking search. Say
we had these optimizations and we are trying to match (co1 ; co2 ; co3) with
(co1' ; co2') (where ; means `TransCo`) One of the coercions disappeared, but
which one? Yuck. So, instead of putting this optimization here, we just have
it in OptCoercion.

Note [Don't optimize mkCoherenceCo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
One would expect to use an easy optimization in mkCoherenceCo: we would want
  (CoherenceCo (CoherenceCo co1 co2) co3)
to become
  (CoherenceCo co1 (mkTransCo co2 co3))

This would be completely sound, and in fact it is done in OptCoercion. But
we *can't* do it here. This is because these smart constructors must be
invertible, in some sense. In the matching algorithm, we must consider all
optimizations that can happen during substitution. Because mkCoherenceCo
is used in substitution, if we did this optimization, the match function
would need to look for substitutions that yield this optimization. The
problem is that these substitutions are hard to find, because the mkTransCo
itself might be optimized. The basic problem is that it is hard to figure
out what co2 could possibly be from the optimized version. So, we don't
do the optimization.

Note [Optimizing mkSymCo is OK]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given the previous two notes, the implementation of mkSymCo seems fishy.
Why is it OK to optimize this one? Because the optimizations don't require
backtracking search to invert, essentially. Say we are matching (SymCo co1)
with co2. If co2 is (SymCo co2'), then we just match co1 with co2'. If
co2 is (UnsafeCo ty1 ty2), then we match co1 with (UnsafeCo ty2 ty1). Otherwise,
we match co1 with (SymCo co2) -- the only way to get a coercion headed by
something other than SymCo or UnsafeCo is the SymCo (SymCo ..) optimization.
Also, critically, it is impossible to get a coercion headed by SymCo or
UnsafeCo by this optimization. (Contrast to the missing optimization in
mkTransCo, which could produce a TransCo.) So, we can keep these here. Phew.

\begin{code}
mkReflCo :: Type -> Coercion
mkReflCo ty
  = ASSERT( not $ isCoercionTy ty )
    Refl ty

-- | Apply a type constructor to a list of coercions.
mkTyConAppCo :: TyCon -> [CoercionArg] -> Coercion
mkTyConAppCo tc cos
	       -- Expand type synonyms
  | Just (tv_co_prs, rhs_ty, leftover_cos) <- tcExpandTyCon_maybe tc cos
  = mkAppCos (liftCoSubst tv_co_prs rhs_ty) leftover_cos

  | Just tys <- traverse isReflCo_maybe cos 
  = Refl (mkTyConApp tc tys)	-- See Note [Refl invariant]

  | otherwise = TyConAppCo tc cos

-- | Make a function 'Coercion' between two other 'Coercion's
mkFunCo :: Coercion -> Coercion -> Coercion
mkFunCo co1 co2 = mkTyConAppCo funTyCon [TyCoArg co1, TyCoArg co2]

-- | Apply a 'Coercion' to another 'CoercionArg'.
mkAppCo :: Coercion -> CoercionArg -> Coercion
mkAppCo (Refl ty1) arg
  | Just ty2 <- isReflLike_maybe arg
  = Refl (mkAppTy ty1 ty2)
mkAppCo (Refl (TyConApp tc tys)) co = TyConAppCo tc (map liftSimply tys ++ [co])
mkAppCo (TyConAppCo tc cos) co      = TyConAppCo tc (cos ++ [co])
mkAppCo co1 co2                     = AppCo co1 co2
-- Note, mkAppCo is careful to maintain invariants regarding
-- where Refl constructors appear; see the comments in the definition
-- of Coercion and the Note [Refl invariant] in types/TypeRep.lhs.

-- | Applies multiple 'Coercion's to another 'CoercionArg', from left to right.
-- See also 'mkAppCo'
mkAppCos :: Coercion -> [CoercionArg] -> Coercion
mkAppCos co1 tys = foldl mkAppCo co1 tys

-- | Make a Coercion from a ForAllCoBndr and Coercion
mkForAllCo :: ForAllCoBndr -> Coercion -> Coercion
mkForAllCo cobndr co
  | Refl ty <- co
  = Refl (mkForAllTy (getHomoVar cobndr) ty)
  | otherwise
  = ASSERT( isHomoCoBndr cobndr || not $ isReflCo $ getHeteroKindCo cobndr )
    ForAllCo cobndr co

-- | Make a Coercion quantified over a type variable; the variable has
-- the same type in both types of the coercion
mkForAllCo_TyHomo :: TyVar -> Coercion -> Coercion
mkForAllCo_TyHomo tv (Refl ty) = ASSERT( isTyVar tv ) Refl (mkForAllTy tv ty)
mkForAllCo_TyHomo tv co        = ASSERT( isTyVar tv ) ForAllCo (TyHomo tv) co

-- | Make a Coercion quantified over type variables, potentially of
-- different kinds.
mkForAllCo_Ty :: Coercion -> TyVar -> TyVar -> CoVar -> Coercion -> Coercion
mkForAllCo_Ty _ tv _ _ (Refl ty) = ASSERT( isTyVar tv ) Refl (mkForAllTy tv ty)
mkForAllCo_Ty h tv1 tv2 cv co
  | tyVarKind tv1 `eqType` tyVarKind tv2
  = ASSERT( isReflCo h )
    let co' = substCoWith [tv2,               cv]
                          [mkOnlyTyVarTy tv1, mkReflCo (tyVarKind tv1)] co in
    ASSERT( isTyVar tv1 )
    ForAllCo (TyHomo tv1) co'
  | otherwise
  = ASSERT( isTyVar tv1 && isTyVar tv2 && isCoVar cv )
    ForAllCo (TyHetero h tv1 tv2 cv) co

-- | Make a Coercion quantified over a coercion variable; the variable has
-- the same type in both types of the coercion
mkForAllCo_CoHomo :: CoVar -> Coercion -> Coercion
mkForAllCo_CoHomo cv (Refl ty) = ASSERT( isCoVar cv ) Refl (mkForAllTy cv ty)
mkForAllCo_CoHomo cv co        = ASSERT( isCoVar cv ) ForAllCo (CoHomo cv) co

-- | Make a Coercion quantified over two coercion variables, possibly of
-- different kinds
mkForAllCo_Co :: Coercion -> CoVar -> CoVar -> Coercion -> Coercion
mkForAllCo_Co _ cv _ (Refl ty) = ASSERT( isCoVar cv ) Refl (mkForAllTy cv ty)
mkForAllCo_Co h cv1 cv2 co
  | coVarKind cv1 `eqType` coVarKind cv2
  = ASSERT( isReflCo h )
    let co' = substCoWith [cv2] [mkCoVarCo cv1] co in
    ASSERT( isCoVar cv1 )
    ForAllCo (CoHomo cv1) co'
  | otherwise
  = ASSERT( isCoVar cv1 && isCoVar cv2 )
    ForAllCo (CoHetero h cv1 cv2) co

mkCoVarCo :: CoVar -> Coercion
-- cv :: s ~# t
mkCoVarCo cv
  | ty1 `eqType` ty2 = Refl ty1
  | otherwise        = CoVarCo cv
  where
    (ty1, ty2) = coVarTypes cv

mkFreshCoVar :: InScopeSet -> Type -> Type -> CoVar
mkFreshCoVar in_scope ty1 ty2
  = let cv_uniq = mkCoVarUnique 31 -- arbitrary number
        cv_name = mkSystemVarName cv_uniq (mkFastString "c") in
    uniqAway in_scope $ mkCoVar cv_name (mkCoercionType ty1 ty2)

mkAxInstCo :: CoAxiom br -> Int -> [Type] -> Coercion
-- mkAxInstCo can legitimately be called over-staturated; 
-- i.e. with more type arguments than the coercion requires
mkAxInstCo ax index tys
  | arity == n_tys = mkAxiomInstCo ax_br index rtys
  | otherwise      = ASSERT( arity < n_tys )
                     foldl mkAppCo (mkAxiomInstCo ax_br index (take arity rtys))
                                   (drop arity rtys)
  where
    n_tys = length tys
    arity = coAxiomArity ax index
    rtys  = map liftSimply tys
    ax_br = toBranchedAxiom ax

-- worker function; just checks to see if it should produce Refl
mkAxiomInstCo :: CoAxiom br -> Int -> [CoercionArg] -> Coercion
mkAxiomInstCo ax index args
  = ASSERT( coAxiomArity ax index == length args )
    let co           = AxiomInstCo ax_br index rtys
        Pair ty1 ty2 = coercionKind co in
    if ty1 `eqType` ty2
    then Refl ty1
    else co

-- to be used only with unbranched axioms
mkUnbranchedAxInstCo :: CoAxiom Unbranched -> [Type] -> Coercion
mkUnbranchedAxInstCo ax tys
  = mkAxInstCo ax 0 tys

mkAxInstLHS, mkAxInstRHS :: CoAxiom br -> BranchIndex -> [Type] -> Type
-- Instantiate the axiom with specified types,
-- returning the instantiated RHS
-- A companion to mkAxInstCo: 
--    mkAxInstRhs ax index tys = snd (coercionKind (mkAxInstCo ax index tys))
mkAxInstLHS ax index tys
  | CoAxBranch { cab_tvs = tvs, cab_lhs = lhs } <- coAxiomNthBranch ax index
  , (tys1, tys2) <- splitAtList tvs tys
  = ASSERT( tvs `equalLength` tys1 ) 
    mkTyConApp (coAxiomTyCon ax) (substTysWith tvs tys1 lhs ++ tys2)
  where

mkAxInstRHS ax index tys
  | CoAxBranch { cab_tvs = tvs, cab_rhs = rhs } <- coAxiomNthBranch ax index
  , (tys1, tys2) <- splitAtList tvs tys
  = ASSERT( tvs `equalLength` tys1 ) 
    mkAppTys rhs' tys2
  where
    branch       = coAxiomNthBranch ax index
    tvs          = coAxBranchTyCoVars branch
    (tys1, tys2) = splitAtList tvs tys
    mkAppTys (substTyWith tvs tys1 rhs) tys2

mkUnbranchedAxInstRHS :: CoAxiom Unbranched -> [Type] -> Type
mkUnbranchedAxInstRHS ax = mkAxInstRHS ax 0

-- | Manufacture a coercion from thin air. Needless to say, this is
mkAppCo :: Coercion -> Coercion -> Coercion
mkAppCo (Refl ty1) (Refl ty2)       = Refl (mkAppTy ty1 ty2)
mkAppCo (Refl (TyConApp tc tys)) co = TyConAppCo tc (map Refl tys ++ [co])
mkAppCo (TyConAppCo tc cos) co      = TyConAppCo tc (cos ++ [co])
mkAppCo co1 co2                     = AppCo co1 co2
--   not usually safe, but it is used when we know we are dealing with
-- where Refl constructors appear; see the comments in the definition
--   bottom, which is one case in which it is safe.  This is also used

-- | Applies multiple 'Coercion's to another 'Coercion', from left to right.
--   to implement the @unsafeCoerce#@ primitive.  Optimise by pushing
mkAppCos :: Coercion -> [Coercion] -> Coercion
mkAppCos co1 tys = foldl mkAppCo co1 tys

--   down through type constructors.
mkUnsafeCo :: Type -> Type -> Coercion
mkTyConAppCo tc cos
mkUnsafeCo ty1 ty2 | ty1 `eqType` ty2 = Refl ty1
mkUnsafeCo (TyConApp tc1 tys1) (TyConApp tc2 tys2)
  = mkAppCos (liftCoSubst tv_co_prs rhs_ty) leftover_cos

  | tc1 == tc2
  = mkTyConAppCo tc1 (zipWith mkUnsafeCoArg tys1 tys2)

  | otherwise = TyConAppCo tc cos

mkUnsafeCo (FunTy a1 r1) (FunTy a2 r2)
mkFunCo :: Coercion -> Coercion -> Coercion
  = mkFunCo (mkUnsafeCo a1 a2) (mkUnsafeCo r1 r2)

-- | Make a 'Coercion' which binds a variable within an inner 'Coercion'
mkForAllCo :: Var -> Coercion -> Coercion
-- note that a TyVar should be used here, not a CoVar (nor a TcTyVar)
mkForAllCo tv (Refl ty) = ASSERT( isTyVar tv ) Refl (mkForAllTy tv ty)
mkUnsafeCo ty1 ty2 = UnsafeCo ty1 ty2

mkUnsafeCoArg :: Type -> Type -> CoercionArg
mkUnsafeCoArg (CoercionTy co1) (CoercionTy co2) = CoCoArg co1 co2
mkUnsafeCoArg ty1 ty2
  = ASSERT( not (isCoercionTy ty1) && not (isCoercionTy ty2) )
    TyCoArg $ UnsafeCo ty1 ty2

-- | Create a symmetric version of the given 'Coercion' that asserts
--   equality between the same types but in the other "direction", so
--   a kind of @t1 ~ t2@ becomes the kind @t2 ~ t1@.
mkSymCo :: Coercion -> Coercion

-- Do a few simple optimizations, but don't bother pushing occurrences
-- of symmetry to the leaves; the optimizer will take care of that.
-- See Note [Optimizing mkSymCo is OK]
mkSymCo co@(Refl {})              = co
mkSymCo    (UnsafeCo ty1 ty2)    = UnsafeCo ty2 ty1
mkSymCo    (SymCo co)            = co
mkSymCo co                       = SymCo co

-- | Create a new 'Coercion' by composing the two given 'Coercion's transitively.
mkTransCo :: Coercion -> Coercion -> Coercion
-- See Note [Don't optimize mkTransCo]
mkTransCo co1 co2
  | Pair s1 _s2 <- coercionKind co1
  , Pair _t1 t2 <- coercionKind co2
  , s1 `eqType` t2
  = ASSERT( _s2 `eqType` _t1 )
    Refl s1
mkTransCo co1 co2     = TransCo co1 co2

mkNthCo :: Int -> Coercion -> Coercion
mkNthCo n (Refl ty) = ASSERT( ok_tc_app ty n ) 
                      Refl (tyConAppArgN n ty)
mkNthCo n co 
  | Just (tv1, _) <- splitForAllTy_maybe ty1
  , Just (tv2, _) <- splitForAllTy_maybe ty2
  , tyVarKind tv1 `eqType` tyVarKind tv2
  = Refl (tyVarKind tv1)

  | Just (_tc1, tys1) <- splitTyConApp_maybe ty1
  , Just (_tc2, tys2) <- splitTyConApp_maybe ty2
  , ASSERT( n < length tys1 && n < length tys2 )
    (tys1 !! n) `eqType` (tys2 !! n)
  = Refl (tys1 !! n)

  | otherwise
  = NthCo n co
  where
    Pair ty1 ty2 = coercionKind co

ok_tc_app :: Type -> Int -> Bool
ok_tc_app ty n
  | Just (_, tys) <- splitTyConApp_maybe ty
  = tys `lengthExceeds` n
  | isForAllTy ty  -- nth:0 pulls out a kind coercion from a hetero forall
  = n == 0
  | otherwise
  = False

mkLRCo :: LeftOrRight -> Coercion -> Coercion
mkLRCo lr (Refl ty) = Refl (pickLR lr (splitAppTy ty))
mkLRCo lr co    
  | ty1 `eqType` ty2
  = Refl ty1
  | otherwise
  = LRCo lr co
  where Pair ty1 ty2 = (pickLR lr . splitAppTy) <$> coercionKind co

-- | Instantiates a 'Coercion'.
mkInstCo :: Coercion -> CoercionArg -> Coercion
mkInstCo co arg = let result = InstCo co arg
                      Pair ty1 ty2 = coercionKind result in
                  if ty1 `eqType` ty2
                  then Refl ty1
                  else result

-- See Note [Don't optimize mkCoherenceCo]
mkCoherenceCo :: Coercion -> Coercion -> Coercion
mkCoherenceCo co1 co2     = let result = CoherenceCo co1 co2
                                Pair ty1 ty2 = coercionKind result in
                            if ty1 `eqType` ty2
                            then Refl ty1
                            else result

-- | A CoherenceCo c1 c2 applies the coercion c2 to the left-hand type
-- in the kind of c1. This function uses sym to get the coercion on the 
-- right-hand type of c1. Thus, if c1 :: s ~ t, then mkCoherenceRightCo c1 c2
-- has the kind (s ~ (t |> c2))
--   down through type constructors.
mkCoherenceRightCo :: Coercion -> Coercion -> Coercion
mkCoherenceRightCo c1 c2 = mkSymCo (mkCoherenceCo (mkSymCo c1) c2)
mkUnsafeCo (TyConApp tc1 tys1) (TyConApp tc2 tys2)
  | tc1 == tc2
  = mkTyConAppCo tc1 (zipWith mkUnsafeCo tys1 tys2)

-- | An explictly directed synonym of mkCoherenceCo
mkCoherenceLeftCo :: Coercion -> Coercion -> Coercion
mkCoherenceLeftCo = mkCoherenceCo
  = mkFunCo (mkUnsafeCo a1 a2) (mkUnsafeCo r1 r2)

infixl `mkCoherenceCo` 5
infixl `mkCoherenceRightCo` 5
infixl `mkCoherenceLeftCo` 5

mkKindCo :: Coercion -> Coercion
mkKindCo (Refl ty) = Refl (typeKind ty)
mkKindCo co
  | Pair ty1 ty2 <- coercionKind co
  , typeKind ty1 `eqType` typeKind ty2
  = Refl (typeKind ty1)
  | otherwise
  = KindCo co
\end{code}

%************************************************************************
%*                                                                      *
   ForAllCoBndr
%*                                                                      *
%************************************************************************

\begin{code}

-- | Makes homogeneous ForAllCoBndr, choosing between TyHomo and CoHomo
-- based on the nature of the TyCoVar
mkHomoCoBndr :: TyCoVar -> ForAllCoBndr
mkHomoCoBndr v
  | isTyVar v = TyHomo v
  | otherwise = CoHomo v

getHomoVar :: ForAllCoBndr -> TyCoVar
getHomoVar cobndr
  | Just v <- getHomoVar_maybe = v
  | otherwise                  = pprPanic "getHomoVar" (ppr cobndr)

getHomoVar_maybe :: ForAllCoBndr -> TyCoVar
getHomoVar_maybe (TyHomo tv) = Just tv
getHomoVar_maybe (CoHomo cv) = Just cv
getHomoVar_maybe _           = Nothing

splitHeteroCoBndr_maybe :: ForAllCoBndr -> Maybe (Coercion, TyCoVar, TyCoVar)
splitHeteroCoBndr_maybe (TyHetero eta tv1 tv2 _) = Just (eta, tv1, tv2)
splitHeteroCoBndr_maybe (TyHetero eta cv1 cv2)   = Just (eta, cv1, cv2)
splitHeteroCoBndr_maybe _                        = Nothing

isHomoCoBndr :: ForAllCoBndr -> Bool
isHomoCoBndr (TyHomo {}) = True
isHomoCoBndr (CoHomo {}) = True
isHomoCoBndr _           = False

getHeteroKindCo :: ForAllCoBndr -> Coercion
getHeteroKindCo (TyHetero eta _ _ _) = eta
getHeteroKindCo (CoHetero eta _ _) = eta
getHeteroKindCo cobndr = pprPanic "getHeteroKindCo" (ppr cobndr)

mkTyHeteroCoBndr :: Coercion -> TyVar -> TyVar -> CoVar -> ForAllCoBndr
mkTyHeteroCoBndr h tv1 tv2 cv
  = ASSERT( _hty1 `eqType` (tyVarKind tv1) )
    ASSERT( _hty2 `eqType` (tyVarKind tv2) )
    ASSERT( coVarKind cv `eqType` (mkCoercionType (mkOnlyTyVarTy tv1) (mkOnlyTyVarTy tv2)) )
    TyHetero h tv1 tv2 cv
    where Pair _hty1 _hty2 = coercionKind h

-------------------------------

-- like mkKindCo, but aggressively & recursively optimizes to avoid using
-- a KindCo constructor.
promoteCoercion :: Coercion -> Coercion

-- First cases handles anything that should yield refl. The ASSERT( False )s throughout
-- are these cases explicitly, but they should never fire.
promoteCoercion co
  | Pair ty1 ty2 <- coercionKind co
  , (typeKind ty1) `eqType` (typeKind ty2)
  = mkReflCo (typeKind ty1)

-- These should never return refl.
promoteCoercion (Refl ty) = ASSERT( False ) mkReflCo (typeKind ty)
promoteCoercion g@(TyConAppCo tc args)
  | Just co' <- instCoercions (mkReflCo (tyConKind tc)) args
  = co'
  | otherwise
  = mkKindCo g
promoteCoercion g@(AppCo co arg)
  | Just co' <- instCoercion (promoteCoercion co) arg
  = co'
  | otherwise
  = mkKindCo g
promoteCoercion (ForAllCo _ _)     = ASSERT( False ) mkReflCo liftedTypeKind
promoteCoercion g@(CoVarCo {})     = mkKindCo g
promoteCoercion g@(AxiomInstCo {}) = mkKindCo g
promoteCoercion g@(UnsafeCo {})    = mkKindCo g
promoteCoercion (SymCo co)         = mkSymCo (promoteCoercion co)
promoteCoercion (TransCo co1 co2)  = mkTransCo (promoteCoercion co1)
                                               (promoteCoercion co2)
promoteCoercion g@(NthCo n co)
  | Just (_, args) <- splitTyConAppCo_maybe co
  , n < length args
  = case args !! n of
      TyCoArg co1 -> promoteCoercion co1
      CoCoArg co1 co2 -> undefined -- TODO (RAE): Fix this
  | Just (cobndr, co1) <- splitForAllCo_maybe co
  , n == 0
  = ASSERT( False ) mkReflCo liftedTypeKind
  | otherwise
  = mkKindCo g
promoteCoercion g@(LRCo lr co)
  | Just (lco, rarg) <- splitAppCo_maybe
  = case lr of
      CLeft  -> promoteCoercion lco
      CRight -> case rarg of
        TyCoArg co1 -> promoteCoercion co1
        CoCoArg co1 co2 -> undefined -- TODO (RAE): Fix this
  | otherwise
  = mkKindCo g
promoteCoercion (InstCo _ _)      = ASSERT( False ) mkReflCo liftedTypeKind
promoteCoercion (CoherenceCo g h) = (mkSymCo cor) `mkTransCo` promoteCoercion g
promoteCoercion (KindCo co)       = ASSERT( False ) mkReflCo liftedTypeKind

-- say g = promoteCoercion h. Then, instCoercion g w yields Just g',
-- where g' = promoteCoercion (h w)
-- fails if this is not possible, if g coerces between a forall and an ->
instCoercion :: Coercion -> CoercionArg -> Maybe Coercion
instCoercion g w
  | isForAllTy ty1 && isForAllTy ty2
  = Just $ mkInstCo g w
  | isFunTy ty1 && isFunTy ty2
  = Just $ mkNthCo 1 g -- extract result type, which is the 2nd argument to (->)
  | otherwise -- one forall, one funty...
  = Nothing
  where
    Pair ty1 ty2 = coercionKind g

instCoercions :: Coercion -> [CoercionArg] -> Maybe Coercion
instCoercions = foldM instCoercion

-- | Creates a new coercion with both of its types casted by different casts
-- castCoercionKind g h1 h2, where g :: t1 ~ t2, has type (t1 |> h1) ~ (t2 |> h2)
castCoercionKind :: Coercion -> Coercion -> Coercion -> Coercion
castCoercionKind g h1 h2 = g `mkCoherenceLeftCo` h1 `mkCoherenceRightCo` h2

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
  where branch = CoAxBranch { cab_loc = getSrcSpan name
                            , cab_tvs = tvs
                            , cab_lhs = mkTyCoVarTys tvs
                            , cab_rhs = rhs_ty }

mkPiCos :: [Var] -> Coercion -> Coercion
mkPiCos vs co = foldr mkPiCo co vs

mkPiCo  :: Var -> Coercion -> Coercion
mkPiCo v co | isTyVar v = mkForAllCo_TyHomo v co
            | isCoVar v = mkForAllCo_CoHomo v co
            | otherwise = mkFunCo (mkReflCo (varType v)) co

-- mkCoCast (c :: s1 ~# t1) (g :: (s1 ~# s2) ~# (t1 ~# t2)) :: t2 ~# t2
mkCoCast :: Coercion -> Coercion -> Coercion
-- (mkCoCast (c :: s1 ~# t1) (g :: (s1 ~# t1) ~# (s2 ~# t2)
mkCoCast c g
  = mkSymCo g1 `mkTransCo` c `mkTransCo` g2
  where
       -- g  :: (s1 ~# s2) ~# (t1 ~#  t2)
       -- g1 :: s1 ~# t1
       -- g2 :: s2 ~# t2
    [_reflk1, _reflk2, g1, g2] = decomposeCo 4 g
            -- Remember, (~#) :: forall k1 k2. k1 -> k2 -> *
            -- so it takes *four* arguments, not two
\end{code}

%************************************************************************
%*                                                                      *
   CoercionArgs
%*                                                                      *
%************************************************************************

\begin{code}
isTyCoArg :: CoercionArg -> Bool
isTyCoArg (TyCoArg _) = True
isTyCoArg _           = False

isCoCoArg :: CoercionArg -> Bool
isCoCoArg (CoCoArg _) = True
isCoCoArg _           = False

stripTyCoArg :: CoercionArg -> Coercion
stripTyCoArg (TyCoArg co) = co
stripTyCoArg arg          = pprPanic "stripTyCoArg" (ppr arg)

stripCoCoArg :: CoercionArg -> Pair Coercion
stripCoCoArg (CoCoArg co1 co2) = Pair co1 co2
stripCoCoArg arg               = pprPanic "stripCoCoArg" (ppr arg)

-- | Makes a suitable CoercionArg representing the passed-in variable
-- during a lifting-like substitution
mkCoArgForVar :: TyCoVar -> CoercionArg
mkCoArgForVar v
  | isTyVar v = TyCoArg $ mkReflCo $ mkOnlyTyVarTy v
  | otherwise = CoCoArg (mkCoVarCo v) (mkCoVarCo v)
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
    Just (substTyWith tvs tys ty, mkUnbranchedAxInstCo co_tc tys)
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

eqCoercion :: Coercion -> Coercion -> Bool
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
-- | A substitution of 'Coercion's for 'CoVar's (OR 'TyVar's, when
--   doing a \"lifting\" substitution)
type CvSubstEnv = VarEnv Coercion

emptyCvSubstEnv :: CvSubstEnv
emptyCvSubstEnv = emptyVarEnv

data CvSubst 		
  = CvSubst InScopeSet 	-- The in-scope type variables
	    TvSubstEnv	-- Substitution of types
            CvSubstEnv  -- Substitution of coercions

instance Outputable CvSubst where
  ppr (CvSubst ins tenv cenv)
    = brackets $ sep[ ptext (sLit "CvSubst"),
		      nest 2 (ptext (sLit "In scope:") <+> ppr ins), 
		      nest 2 (ptext (sLit "Type env:") <+> ppr tenv),
		      nest 2 (ptext (sLit "Coercion env:") <+> ppr cenv) ]

emptyCvSubst :: CvSubst
emptyCvSubst = CvSubst emptyInScopeSet emptyVarEnv emptyVarEnv

isEmptyCvSubst :: CvSubst -> Bool
isEmptyCvSubst (CvSubst _ tenv cenv) = isEmptyVarEnv tenv && isEmptyVarEnv cenv

getCvInScope :: CvSubst -> InScopeSet
getCvInScope (CvSubst in_scope _ _) = in_scope

zapCvSubstEnv :: CvSubst -> CvSubst
zapCvSubstEnv (CvSubst in_scope _ _) = CvSubst in_scope emptyVarEnv emptyVarEnv

cvTvSubst :: CvSubst -> TvSubst
cvTvSubst (CvSubst in_scope tvs _) = TvSubst in_scope tvs

tvCvSubst :: TvSubst -> CvSubst
tvCvSubst (TvSubst in_scope tenv) = CvSubst in_scope tenv emptyCvSubstEnv

extendTvSubst :: CvSubst -> TyVar -> Type -> CvSubst
extendTvSubst (CvSubst in_scope tenv cenv) tv ty
  = CvSubst in_scope (extendVarEnv tenv tv ty) cenv

extendCvSubstAndInScope :: CvSubst -> CoVar -> Coercion -> CvSubst
-- Also extends the in-scope set
extendCvSubstAndInScope (CvSubst in_scope tenv cenv) cv co
  = CvSubst (in_scope `extendInScopeSetSet` tyCoVarsOfCo co)
            tenv
            (extendVarEnv cenv cv co)

substCoVarBndr :: CvSubst -> CoVar -> (CvSubst, CoVar)
substCoVarBndr subst@(CvSubst in_scope tenv cenv) old_var
  = ASSERT( isCoVar old_var )
    (CvSubst (in_scope `extendInScopeSet` new_var) tenv new_cenv, new_var)
  where
    -- When we substitute (co :: t1 ~ t2) we may get the identity (co :: t ~ t)
    -- In that case, mkCoVarCo will return a ReflCoercion, and
    -- we want to substitute that (not new_var) for old_var
    new_co    = mkCoVarCo new_var
    no_change = new_var == old_var && not (isReflCo new_co)

    new_cenv | no_change = delVarEnv cenv old_var
             | otherwise = extendVarEnv cenv old_var new_co

    new_var = uniqAway in_scope subst_old_var
    subst_old_var = mkCoVar (varName old_var) (substTy subst (varType old_var))
		  -- It's important to do the substitution for coercions,
		  -- because they can have free type variables

substTyVarBndr :: CvSubst -> TyVar -> (CvSubst, TyVar)
substTyVarBndr (CvSubst in_scope tenv cenv) old_var
  = case Type.substTyVarBndr (TvSubst in_scope tenv) old_var of
      (TvSubst in_scope' tenv', new_var) -> (CvSubst in_scope' tenv' cenv, new_var)

mkCvSubst :: InScopeSet -> [(Var,Coercion)] -> CvSubst
mkCvSubst in_scope prs = CvSubst in_scope Type.emptyTvSubstEnv (mkVarEnv prs)

zipOpenCvSubst :: [Var] -> [Coercion] -> CvSubst
zipOpenCvSubst vs cos
  | debugIsOn && (length vs /= length cos)
  = pprTrace "zipOpenCvSubst" (ppr vs $$ ppr cos) emptyCvSubst
  | otherwise 
  = CvSubst (mkInScopeSet (tyCoVarsOfCos cos)) emptyTvSubstEnv (zipVarEnv vs cos)

substCoWithTy :: InScopeSet -> TyVar -> Type -> Coercion -> Coercion
substCoWithTy in_scope tv ty = substCoWithTys in_scope [tv] [ty]

substCoWithTys :: InScopeSet -> [TyVar] -> [Type] -> Coercion -> Coercion
substCoWithTys in_scope tvs tys co
  | debugIsOn && (length tvs /= length tys)
eqCoercion c1 c2 = isEqual $ cmpCoercion c1 c2
  | otherwise 
  = ASSERT( length tvs == length tys )
    substCo (CvSubst in_scope (zipVarEnv tvs tys) emptyVarEnv) co

-- | Substitute within a 'Coercion'
eqCoercionX :: RnEnv2 -> Coercion -> Coercion -> Bool
substCo subst co | isEmptyCvSubst subst = co
eqCoercionX env c1 c2 = isEqual $ cmpCoercionX env c1 c2

-- | Substitute within several 'Coercion's
cmpCoercion :: Coercion -> Coercion -> Ordering
cmpCoercion c1 c2 = cmpCoercionX rn_env c1 c2
  where rn_env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfCo c1 `unionVarSet` tyCoVarsOFCo c2))

cmpCoercionX :: RnEnv2 -> Coercion -> Coercion -> Ordering
cmpCoercionX env (Refl ty1)                   (Refl ty2) = cmpTypeX env ty1 ty2
cmpCoercionX env (TyConAppCo tc1 args1)       (TyConAppCo tc2 args2)
  = (tc1 `cmpTc` tc2) `thenCmp` cmpCoercionArgsX env args1 args2
cmpCoercionX env (AppCo co1 arg1)             (AppCo co2 arg2)
  = cmpCoercionX env co1 co2 `thenCmp` cmpCoercionArgX env arg1 arg2
cmpCoercionX env (ForAllCo cobndr1 co1)       (ForAllCo cobndr2 co2)
  = cmpCoBndrX env cobndr1 cobndr2 `thenCmp`
    cmpCoercionX (rnCoBndr2 env cobndr1 cobndr2) co1 co2
cmpCoercionX env (CoVarCo cv1)                (CoVarCo cv2)
  = rnOccL env cv1 `compare` rnOccR env cv2
cmpCoercionX env (AxiomInstCo ax1 ind1 args1) (AxiomInstCo ax2 ind2 args2)
  = (ax1 `cmpCoAx` ax2) `thenCmp`
    (ind1 `compare` ind2) `thenCmp`
    cmpCoercionArgsX env args1 args2
cmpCoercionX env (UnsafeCo tyl1 tyr1)         (UnsafeCo tyl2 tyr2)
  = cmpTypeX env tyl1 tyl2 `thenCmp` cmpTypeX env tyr1 tyr2
cmpCoercionX env (SymCo co1)                  (SymCo co2)
  = cmpCoercionX env co1 co2
cmpCoercionX env (TransCo col1 cor1)          (TransCo col2 cor2)
  = cmpCoercionX env col1 col2 `thenCmp` cmpCoercionX env cor1 cor2
cmpCoercionX env (NthCo n1 co1)               (NthCo n2 co2)
  = (n1 `compare` n2) `thenCmp` cmpCoercionX env co1 co2
cmpCoercionX env (InstCo co1 arg1)            (InstCo co2 arg2)
  = cmpCoercionX co1 co2 `thenCmp` cmpCoercionArgX arg1 arg2
cmpCoercionX env (CoherenceCo col1 cor1)      (CoherenceCo col2 cor2)
  = cmpCoercionX col1 col2 `thenCmp` cmpCoercionX cor1 cor2
cmpCoercionX env (KindCo co1)                 (KindCo co2)
  = cmpCoercionX env co1 co2

-- Deal with the rest, in constructor order
-- Refl < TyConAppCo < AppCo < ForAllCo < CoVarCo < AxiomInstCo <
--  UnsafeCo < SymCo < TransCo < NthCo < LRCo < InstCo < CoherenceCo < KindCo
cmpCoercionX _ co1 co2
  = (get_rank co1) `compare` (get_rank co2)
  where get_rank (Refl {})        = 0
        get_rank (TyConAppCo {})  = 1
        get_rank (AppCo {})       = 2
        get_rank (ForAllCo {})    = 3
        get_rank (CoVarCo {})     = 4
        get_rank (AxiomInstCo {}) = 5
        get_rank (UnsafeCo {})    = 6
        get_rank (SymCo {})       = 7
        get_rank (TransCo {})     = 8
        get_rank (NthCo {})       = 9
        get_rank (LRCo {})        = 10
        get_rank (InstCo {})      = 11
        get_rank (CoherenceCo {}) = 12
        get_rank (KindCo {})      = 13

cmpCoercionArgX :: RnEnv2 -> CoercionArg -> CoercionArg -> Ordering
    go (Refl ty)             = Refl $! go_ty ty
    go (TyConAppCo tc cos)   = let args = map go cos
cmpCoercionArgX env (TyCoArg co1)       (TyCoArg co2)
  = cmpCoercionX env co1 co2
    go (ForAllCo tv co)      = case substTyVarBndr subst tv of
cmpCoercionArgX env (CoCoArg col1 cor1) (CoCoArg col2 cor2)
                                   ForAllCo tv' $! subst_co subst' co
    go (CoVarCo cv)          = substCoVar subst cv
    go (AxiomInstCo con ind cos) = AxiomInstCo con ind $! map go cos
  = cmpCoercionX env col1 col2 `thenCmp` cmpCoercionX env cor1 cor2
    go (SymCo co)            = mkSymCo (go co)
cmpCoercionArgX _ (TyCoArg {}) (CoCoArg {}) = LT
    go (NthCo d co)          = mkNthCo d (go co)
cmpCoercionArgX _ (CoCoArg {}) (TyCoArg {}) = GT
    go (InstCo co ty)        = mkInstCo (go co) $! go_ty ty

cmpCoercionArgsX :: RnEnv2 -> [CoercionArg] -> [CoercionArg] -> Ordering
cmpCoercionArgsX _ [] [] = EQ
cmpCoercionArgsX env (arg1:args1) (arg2:args2)
  = cmpCoercionArgX env arg1 arg2 `thenCmp` cmpCoercionArgsX env args1 args2
cmpCoercionArgsX _ [] _  = LT
cmpCoercionArgsX _ _  [] = GT

cmpCoAx :: CoAxiom -> CoAxiom -> Ordering
cmpCoAx ax1 ax2 = (coAxiomUnique ax1) `compare` (coAxiomUnique ax2)

cmpCoBndr :: RnEnv2 -> ForAllCoBndr -> ForAllCoBndr -> Ordering
cmpCoBndr env (TyHomo tv1) (TyHomo tv2)
  = cmpTypeX env (tyVarKind tv1) (tyVarKind tv2)
cmpCoBndr env (TyHetero co1 tvl1 tvr1 cv1) (TyHetero co2 tvl2 tvr2 cv2)
  = cmpCoercionX env co1 co2 `thenCmp`
    cmpTypeX env (tyVarKind tvl1) (tyVarKind tvl2) `thenCmp`
    cmpTypeX env (tyVarKind tvr1) (tyVarKind tvr2) `thenCmp`
    cmpTypeX env (coVarKind cv1)  (coVarKind cv2)
cmpCoBndr env (CoHomo cv1) (CoHomo cv2)
  = cmpTypeX env (coVarKind cv1) (coVarKind cv2)
cmpCoBndr env (CoHetero co1 cvl1 cvr1) (CoHetero co2 cvl2 cvr2)
  = cmpCoercionX env co1 co2 `thenCmp`
    cmpTypeX env (coVarKind cvl1) (coVarKind cvl2) `thenCmp`
    cmpTypeX env (coVarKind cvr1) (coVarKind cvr2)
cmpCoBndr _ cobndr1 cobndr2
  = (get_rank cobndr1) `compare` (get_rank cobndr2)
  where get_rank (TyHomo {})   = 0
        get_rank (TyHetero {}) = 1
        get_rank (CoHomo {})   = 2
        get_rank (CoHetero {}) = 3

rnCoBndr2 :: RnEnv2 -> ForAllCoBndr -> ForAllCoBndr -> RnEnv2
rnCoBndr2 env cobndr1 cobndr2
  = foldl2 rnBndr2 (coBndrVars cobndr1) (coBndrVars cobndr2)
\end{code}

%************************************************************************
%*									*
                   "Lifting" substitution
	   [(TyCoVar,CoercionArg)] -> Type -> Coercion
%*                                                                      *
%************************************************************************

Note [Lifting Contexts]
~~~~~~~~~~~~~~~~~~~~~~~
Say we have an expression like this, where K is a constructor of the type
T:

case (K a b |> co) of ...

The scrutinee is not an application of a constructor -- it is a cast. Thus,
we want to be able to push the coercion inside the arguments to K (a and b,
in this case) so that the top-level structure of the scrutinee is a
constructor application. In the presence of kind coercions, this is a bit
of a hairy operation. So, we refer you to the paper introducing kind coercions,
available at www.cis.upenn.edu/~sweirich/papers/nokinds-extended.pdf

\begin{code}
data LiftingContext = LC InScopeSet LiftCoEnv

type LiftCoEnv = VarEnv CoercionArg
     -- Maps *type variables* to *coercions* (TyCoArg) and coercion variables
     -- to pairs of coercions (CoCoArg). That's the whole point of this function!

-- See Note [Lifting Contexts]
liftCoSubstWithEx :: [TyCoVar]  -- universally quantified tycovars
                  -> [CoercionArg] -- coercions to substitute for those
                  -> [TyCoVar]  -- existentially quantified tycovars
                  -> [CoreExpr] -- types and coercions to be bound to ex vars
                  -> (Type -> Coercion) -- lifting function
liftCoSubstWithEx univs omegas exs rhos
  = let theta = mkLiftingContext (zipEqual "liftCoSubstWithExU" univs omegas)
        psi   = extendLiftingContext theta (zipEqual "liftCoSubstWithExX" exs rhos)
    in ty_co_subst psi

liftCoSubstWith :: [TyVar] -> [CoercionArg] -> Type -> Coercion
liftCoSubstWith tvs cos ty
  = liftCoSubst (zipEqual "liftCoSubstWith" tvs cos) ty

liftCoSubst :: [(TyVar,CoercionArg)] -> Type -> Coercion
liftCoSubst prs ty
 | null prs  = Refl ty
 | otherwise = ty_co_subst (mkLiftingContext prs) ty

mkLiftingContext :: [(TyCoVar,CoercionArg)] -> LiftingContext
mkLiftingContext prs = LC (mkInScopeSet (tyCoVarsOfCoArgs (map snd prs)))
                          (mkVarEnv prs)

-- See Note [Lifting Contexts]
extendLiftingContext :: LiftingContext -> [(TyCoVar,CoreExpr)] -> LiftingContext
extendLiftingContext lc [] = lc
extendLiftingContext lc@(LC in_scope env) ((v,e):rest)
  | isTyVar v
  , Type ty <- e
  = let lc' = LC (in_scope `extendInScopeSet` tyCoVarsOfType ty)
                 (env `extendVarEnv` v (TyCoArg $ mkSymCo $ mkCoherenceCo
                                         (mkReflCo ty)
                                         (ty_co_subst lc (tyVarKind v))))
    in extendLiftingContext lc' rest
  | Coercion co <- e
  = let (s1, s2) = coVarTypes v
        lc' = LC (in_scope `extendInScopeSet` tyCoVarsOfCo co)
                 (env `extendVarEnv` v (CoCoArg co $
                                         (mkSymCo (ty_co_subst lc s1)) `mkTransCo`
                                         co `mkTransCo`
                                         (ty_co_subst lc s2)))
    in extendLiftingContext lc' rest
  | otherwise
  = pprPanic "extendLiftingContext" (ppr v <+> ptext (sLit "|->") <+> ppr e)

-- | The \"lifting\" operation which substitutes coercions for type
--   variables in a type to produce a coercion.
--
--   For the inverse operation, see 'liftCoMatch' 
ty_co_subst :: LiftingContext -> Type -> Coercion
ty_co_subst lc@(LC in_scope env) ty
  = go ty
  where
    go :: Type -> Coercion
    go ty | tyCoVarsOfType ty `isNotInDomainOf` env = mkReflCo ty
    go (TyVarTy tv)      = liftCoSubstTyVar lc tv
    go (AppTy ty1 ty2)   = mkAppCo (go ty1) (go_arg ty2)
    go (TyConApp tc tys) = mkTyConAppCo tc (map go_arg tys)
                           -- IA0_NOTE: Do we need to do anything
                           -- about kind instantiations? I don't think
                           -- so.  see Note [Kind coercions]
    go (FunTy ty1 ty2)   = mkFunCo (go_arg ty1) (go_arg ty2)
    go (ForAllTy v ty)   = let (lc', cobndr) = liftCoSubstTyCoVarBndr lc v in
                         where
                           mkForAllCo cobndr $! ty_co_subst lc' ty
    go ty@(LitTy {})     = mkReflCo ty
    go (CastTy ty co)    = castCoercionKind (go ty) (substLeftCo lc co)
                                                    (substRightCo lc co)
    go (Coercion co)     = pprPanic "ty_co_subst" (ppr co)

    go_arg :: Type -> CoercionArg
    go_arg (Coercion co) = CoCoArg (substLeftCo lc co) (substRightCo lc co)
    go_arg ty            = TyCoArg (go ty)
liftCoSubstTyVar (LCS _ cenv) tv = lookupVarEnv cenv tv 

    isNotInDomainOf :: VarSet -> VarEnv a -> Bool
    isNotInDomainOf set env
      = noneSet (\v -> elemVarEnv v env) set

    noneSet :: (Var -> Bool) -> VarSet -> Bool
    noneSet f = foldVarSet (\v rest -> rest && (not $ f v)) True

    -- See Note [cast_2_ways]
    cast_2_ways :: Coercion -> Coercion -> Coercion -> Coercion
    cast_2_ways g eta1 eta2 = (mkSymCo ((mkSymCo g) `mkCoherenceCo` eta2))
                              `mkCoherenceCo` eta1

liftCoSubstTyVar :: LiftingContext -> TyVar -> Coercion
liftCoSubstTyVar (LC _ cenv) tv
  | TyCoArg co <- lookupVarEnv_NF cenv tv
  = co
  | otherwise
  = pprPanic "liftCoSubstTyVar" (ppr tv <+> (ptext (sLit "|->")) <+>
                                 ppr (lookupVarEnv_NF cenv tv))

liftCoSubstTyCoVarBndr :: LiftingContext -> TyCoVar
                     -> (LiftingContext, ForAllCoBndr)
liftCoSubstTyCoVarBndr lc@(LC in_scope cenv) old_var
  = (LC (in_scope `extendInScopeSetList` coBndrVars cobndr) new_cenv, cobndr)
  where
    eta = ty_co_subst lc (tyVarKind old_var)
    Pair k1 k2 = coercionKind eta
    new_var = uniqAway in_scope (setVarType old_var k1)

    co_arg_for v
      | isTyVar v = TyCoArg $ mkReflCo $ mkOnlyTyVarTy v
      | otherwise = CoCoArg (mkCoVarCo v) (mkCoVarCo v)

    (new_cenv, cobndr)
      | new_var == old_var
      , k1 `eqType` k2
      = (delVarEnv cenv old_var, mkHomoCoBndr old_var)

      | k1 `eqType` k2
      = ( extendVarEnv cenv old_var (mkCoArgForVar new_var), mkHomoCoBndr new_var)

      | isTyVar old_var
      = let a1 = new_var
            in_scope1 = in_scope `extendInScopeSet` a1
            a2 = uniqAway in_scope1 $ setVarType new_var k2
            in_scope2 = in_scope1 `extendInScopeSet` a2
            c  = mkFreshCoVar in_scope (mkOnlyTyVarTy a1) (mkOnlyTyVarTy a2) in
        ( extendVarEnv cenv old_var (TyCoArg $ mkCoVarCo c)
        , TyHetero eta a1 a2 c )

      | otherwise
      = let cv1 = new_var
            in_scope1 = in_scope `extendInScopeSet` cv1
            cv2 = uniqAway in_scope1 $ setVarType new_var k2 in
        ( extendVarEnv cenv old_var (CoCoArg (mkCoVarCo cv1) (mkCoVarCo cv2))
        , CoHetero eta cv1 cv2 )

-- If [a |-> g] is in the substitution and g :: t1 ~ t2, substitute a for t1
-- If [a |-> (g1, g2)] is in the substitution, substitute a for g1
substLeftCo :: LiftingContext -> Coercion -> Coercion
substLeftCo lc co
  = substCo (lcSubstLeft lc) co

-- Ditto, but for t2 and g2
substRightCo :: LiftingContext -> Coercion -> Coercion
substRightCo lc co
  = substCo (lcSubstRight lc) co

lcSubstLeft :: LiftingContext -> TCvSubst
lcSubstLeft (LC in_scope lc_env) = liftEnvSubstLeft in_scope lc_env

lcSubstRight :: LiftingContext -> TCvSubst
lcSubstRight (LC in_scope lc_env) = liftEnvSubstRight in_scope lc_env

liftEnvSubstLeft :: InScopeSet -> LiftCoEnv -> TCvSubst
liftEnvSubstLeft = liftEnvSubst pFst

liftEnvSubstRight :: InScopeSet -> LiftCoEnv -> TCvSubst
liftEnvSubstRight = liftEnvSubst pSnd

liftEnvSubst :: (forall a. Pair a -> a) -> InScopeSet -> LiftCoEnv -> TCvSubst
liftEnvSubst fn in_scope lc_env
  = mkTCvSubst in_scope tenv cenv
  where
    (tenv0, cenv0) = partitionVarEnv isTyCoArg lc_env
    tenv           = mapVarEnv (fn . coercionKind . stripTyCoArg) tenv0
    cenv           = mapVarEnv (fn . stripCoCoArg) cenv0

zipLiftCoEnv :: RnEnv2 -> LiftCoEnv -> TCvSubst -> TCvSubst -> Maybe LiftCoEnv
zipLiftCoEnv rn_env lc_env (TCvSubst _ l_tenv l_cenv) (TCvSubst _ r_tenv r_cenv)
  = do { lc_env1 <- go_ty lc_env  (varEnvKeys l_tenv)
       ;            go_co lc_env1 (varEnvKeys l_cenv) }
  where
    go_ty :: LiftCoEnv -> TvSubstEnv -> [Unique] -> Maybe LiftCoEnv
    go_ty env r_tenv []
      | isEmptyVarEnv r_tenv
      = Just env
      
      | otherwise -- leftover bindings in renv, but not in lenv
      = Nothing -- See Note [zipLiftCoEnv incomplete]

    go_ty env r_tenv (u:us)
      | Just arg <- lookupVarEnv_Directly env u
      = go_ty env (delVarEnv_Directly r_tenv u) us

      | Just tyl <- lookupVarEnv_Directly l_tenv u
      , Just tyr <- lookupVarEnv_Directly r_tenv u
      , eqTypeX rn_env tyl tyr
      = go_ty (extendVarEnv_Directly env u (TyCoArg (mkReflCo tyr)))
              (delVarEnv_Directly r_tenv u) us

      | otherwise
      = Nothing -- See Note [zipLiftCoEnv incomplete]

    go_co :: LiftCoEnv -> CvSubstEnv -> [Unique] -> Maybe LiftCoEnv
    go_co env r_cenv []
      | isEmptyVarEnv r_cenv
      = Just env

      | otherwise
      = Nothing -- See Note [zipLifCoEnv incomplete]

    go_co env r_cenv (u:us)
      | Just arg <- lookupVarEnv_Directly env u
      = go_co env (delVarEnv_Directly r_cenv u) us

      | Just col <- lookupVarEnv_Directly l_cenv u
      , Just cor <- lookupVarEnv_Directly r_cenv u
      = go_co (extendVarEnv_Directly env u (CoCoArg col cor))
              (delVarEnv_Directly r_cenv u) us

      | otherwise
      = Nothing -- See Note [zipLiftCoEnv incomplete]

-- | all types that are not coercions get lifted into TyCoArg (Refl ty)
-- a coercion (g :: t1 ~ t2) becomes (CoCoArg (Refl t1) (Refl t2)).
-- If you need to convert a Type to a CoercionArg and you are tempted to
-- use (map Refl), then you want this.
liftSimply :: Type -> CoercionArg
liftSimply (CoercionTy co)
  = let (t1, t2) = coercionKind co in
    CoCoArg (mkReflCo t1) (mkReflCo t2)
liftSimply ty = TyCoArg $ mkReflCo ty

\end{code}

Note [zipLiftCoEnv incomplete]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
zipLiftCoEnv attempts to take two TCvSubsts (one for the left side and one for
the right side) and zip them together into a LiftCoEnv. The problem is that,
whenever the two substs disagree on a type mapping, the LiftCoEnv must use a
coercion between the two types. We could theoretically have some pile of
available coercions and sift through them trying to make the right coercion,
but that's a much harder problem than just matching, which is where this is
used. Because this matching is currently (Jan 2013) used only for coercion
optimization, I'm not implementing full coercion inference.

When the two substs disagree on a coercion mapping, though, there is no
problem: we don't need evidence showing coercions agree. We just make the
CoCoArg and carry on.

If the two substs have different sets of bindings, we have a different
problem. Ideally, we would create a new matchable variable for the missing
binding and keep working, but it does not seem worth it to implement this now.
Shout (at Richard Eisenberg, eir@cis.upenn.edu) if this is a problem for you.

Note [Heterogeneous type matching]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Say we have the following in our LiftCoEnv:

[k |-> g]
where g :: k1 ~ k2

Now, we are matching the following:

forall a:k.t <-> forall_g (a1:k1, a2:k2, c:a1~a2).h

We can't just use RnEnv2 the normal way, because there are a different
number of binders on either side. What we want to ensure is that, while
matching t and h, any appearance of a in t is replaced by an appearance
of c in h. So, we just add all the variables separately to the appropriate
sides of the RnEnv2. Then, we augment the substitution to link the renamed
'a' to its lifted coercion, the renamed 'c'. After matching, we then
want to remove this mapping from the substitution before returning.

But, what about the kind of c? Won't its new kind be wrong? Sure, it
will be, but that's OK. If the kind of c ever matters, the occurs check
in the TyVarTy case will fail, because the kind of c mentions local
variables.

The coercion cases follow a similar logic.

Note [ty_co_match CastTy case]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We essentially need to reverse engineer a castCoercionKind to get this to
work. But, the result of the castCoercionKind might, potentially, have been
restructured. So, instead of deconstructing it directly, we just add
more casts to cancel out the ones already there. To have a hope of this
working, though, we want the new casts to cancel out the old ones. If we
just use castCoercionKind again, it does not simplify. (Try it!) On the
other hand, if we use mkCoherenceRightCo *before* mkCoherenceLeftCo, the
optimizations in the mk...Co functions almost do the right thing. The one
problem is the missing optimization in mkCoherenceCo, as described in
Note [Don't optimize mkCoherenceCo]. So, we use the function opt_coh to
implement that optimization in exactly the special case that we need to
cancel out all the coercions. It's a little fiddly, but because there can
be many equivalent coercions, I don't see an easier way.

\begin{code}
-- | 'liftCoMatch' is sort of inverse to 'liftCoSubst'.  In particular, if
--   @liftCoMatch vars ty co == Just s@, then @tyCoSubst s ty == co@.
--   That is, it matches a type against a coercion of the same
--   "shape", and returns a lifting substitution which could have been
--   used to produce the given coercion from the given type.
--   Note that this function is incomplete -- it might return Nothing
--   when there does indeed exist a possible lifting context.
--   See Note [zipLiftCoEnv incomplete]
liftCoMatch :: TyCoVarSet -> Type -> Coercion -> Maybe LiftingContext
liftCoMatch tmpls ty co 
  = case ty_co_match menv emptyVarEnv ty co of
      Just cenv -> Just (LC in_scope cenv)
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

  -- handle Refl case:
  | tyCoVarsOfType ty `isNotInDomainOf` subst
  , Just ty' <- isReflCo_maybe co
  , eqTypeX (me_env menv) ty ty'
  = Just subst

  -- Match a type variable against a non-refl coercion
ty_co_match menv subst (TyVarTy tv1) co
  | Just (TyCoArg co1') <- lookupVarEnv subst tv1' -- tv1' is already bound to co1
  = if eqCoercionX (nukeRnEnvL rn_env) co1' co
    then Just subst
    else Nothing       -- no match since tv1 matches two different coercions

  | tv1' `elemVarSet` me_tmpls menv           -- tv1' is a template var
  = if any (inRnEnvR rn_env) (varSetElems (tyCoVarsOfCo co))
    then Nothing      -- occurs check failed
    else do { subst1 <- ty_co_match menv subst (tyVarKind tv1') (promoteCoercion co)
        -- BAY: I don't think we need to do any kind matching here yet
            ; return (extendVarEnv subst tv1' (TyCoArg co)) }

  | otherwise
                 -- can match is a reflexivity coercion for itself.
		 -- But that case is dealt with already
  = Nothing

  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1

ty_co_match menv subst (AppTy ty1 ty2) co
  | Just (co1, arg2) <- splitAppCo_maybe co	-- c.f. Unify.match on AppTy
  = do { subst' <- ty_co_match menv subst ty1 co1 
       ; ty_co_match_arg menv subst' ty2 arg2 }

ty_co_match menv subst (TyConApp tc1 tys) (TyConAppCo tc2 cos)
  | tc1 == tc2 = ty_co_match_args menv subst tys cos

ty_co_match menv subst (FunTy ty1 ty2) (TyConAppCo tc cos)
  | tc == funTyCon = ty_co_matches menv subst [ty1,ty2] cos

ty_co_match menv subst (ForAllTy tv ty) (ForAllCo cobndr co)
  | TyHomo tv2 <- cobndr
  = ASSERT( isTyVar tv )
    do { subst1 <- ty_co_match menv subst (tyVarKind tv) (mkReflCo $ tyVarKind tv2)
       ; let menv1 = menv { me_env = rnBndr2 (me_env menv) tv tv2 }
       ; ty_co_match menv1 subst1 ty co }

  | TyHetero co1 tvl tvr cv <- cobndr
  = ASSERT( isTyVar tv )
    do { subst1 <- ty_co_match menv subst (tyVarKind tv) co1
         -- See Note [Heterogeneous type matching]
       ; let rn_env0 = me_env menv
             (rn_env1, tv')  = rnBndrL rn_env0 tv
             (rn_env2, _)    = rnBndrR rn_env1 tvl
             (rn_env3, _)    = rnBndrR rn_env2 tvr
             (rn_env4, cv')  = rnBndrR rn_env3 cv
             menv' = menv { me_env = rn_env4 }
             subst2 = extendVarEnv subst1 tv' (TyCoArg (mkCoVarCo cv'))
       ; subst3 <- ty_co_match menv' subst2 ty co
       ; return $ delVarEnv subst3 tv' }

  | CoHomo cv <- cobndr
  = ASSERT( isCoVar tv )
    do { subst1 <- ty_co_match menv subst (coVarKind tv) (mkReflCo $ coVarKind cv)
       ; let rn_env0 = me_env menv
             (rn_env1, tv') = rnBndrL rn_env0 tv
             (rn_env2, cv') = rnBndrR rn_env1 cv
             menv' = menv { me_env = rn_env2 }
             subst2 = extendVarEnv subst1 tv' (mkCoArgForVar cv')
       ; subst3 <- ty_co_match menv' subst2 ty co
       ; return $ delVarEnv subst3 tv' }

  | CoHetero co1 cvl cvr <- cobndr
  = ASSERT( isCoVar tv )
    do { subst1 <- ty_co_match menv subst (coVarKind tv) co1
       ; let rn_env0 = me_env menv
             (rn_env1, tv')  = rnBndrL rn_env0 tv
             (rn_env2, cvl') = rnBndrR rn_env1 cvl
             (rn_env3, cvr') = rnBndrR rn_env2 cvr
             menv' = menv { me_env = rn_env3 }
             subst2 = extendVarEnv subst1 tv' (CoCoArg (mkCoVarCo cvl') (mkCoVarCo cvr'))
       ; subst3 <- ty_co_match menv' subst2 ty co
       ; return $ delVarEnv subst3 tv' }

ty_co_match menv subst (CastTy ty1 co1) co
  | Pair (CastTy _ col) (CastTy _ cor) <- coercionKind co
  = do { subst1 <- ty_co_match_lr menv subst co1 col cor
         -- don't use castCoercionKind! See Note [ty_co_match CastTy case]
       ; ty_co_match menv subst1 ty1
                     (opt_coh (co `mkCoherenceRightCo` (mkSymCo cor)
                                  `mkCoherenceLeftCo` (mkSymCo col))) }
  where
    -- in a very limited number of cases, optimize CoherenceCo
    -- see Note [ty_co_match CastTy case]
    mk_coh co1 (Refl _) = co1
    mk_coh co1 co2      = mkCoherenceCo co1 co2

    opt_coh (SymCo co) = mkSymCo (opt_coh co)
    opt_coh (CoherenceCo (CoherenceCo co1 co2) co3)
      = mk_coh co1 (mkTransCo co2 co3)
    opt_coh (CoherenceCo co1 co2) = mk_coh (opt_coh co1) co2
    opt_coh co = co

ty_co_match _ _ (CoercionTy co) _
  = pprPanic "ty_co_match" (ppr co)

ty_co_match menv subst ty co
  | Just co' <- pushRefl co = ty_co_match menv subst ty co'
  | otherwise               = Nothing

ty_co_match_args :: MatchEnv -> LiftCoEnv -> [Type] -> [CoercionArg]
                 -> Maybe LiftCoEnv
ty_co_match_args menv = matchList (ty_co_match_arg menv)

ty_co_match_arg :: MatchEnv -> LiftCoEnv -> Type -> CoercionArg -> Maybe LiftCoEnv
ty_co_match_arg menv subst ty arg
  | TyCoArg co <- arg
  = ty_co_match menv subst ty co
  | CoercionTy co1 <- ty
  , CoCoArg col cor <- arg
  = ty_co_match_lr menv subst co1 col cor
  | otherwise
  = pprPanic "ty_co_match_arg" (ppr ty <+> ptext (sLit "<->") <+> ppr arg)

ty_co_match_lr :: MatchEnv -> LiftCoEnv
               -> Coercion -> Coercion -> Coercion -> Maybe LiftCoEnv
ty_co_match_lr menv subst co1 col cor
  = do { let subst_left  = liftEnvSubstLeft  in_scope subst
             subst_right = liftEnvSubstRight in_scope subst
       ; tcvsubst1 <- tcMatchCoX tmpl_vars subst_left  co1 col
       ; tcvsubst2 <- tcMatchCoX tmpl_vars subst_right co1 cor
       ; zipLiftCoEnv rn_env subst tcvsubst1 tcvsubst2 }
  where
    ME { me_tmpls = tmpl_vars
       , me_env   = rn_env } = menv
  
pushRefl :: Coercion -> Maybe Coercion
pushRefl (Refl (AppTy ty1 ty2))   = Just (AppCo (Refl ty1) (liftSimply ty2))
pushRefl (Refl (FunTy ty1 ty2))   = Just (TyConAppCo funTyCon [liftSimply ty1, liftSimply ty2])
pushRefl (Refl (TyConApp tc tys)) = Just (TyConAppCo tc (map liftSimply tys))
pushRefl (Refl (ForAllTy tv ty))
  | isTyVar tv                    = Just (ForAllCo (TyHomo tv) (Refl ty))
  | otherwise                     = Just (ForAllCo (CoHomo tv) (Refl ty))
pushRefl (Refl (CastTy ty co))    = Just ((mkSymCo co) `TransCo` (Refl ty) `TransCo` co)
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
seqCo (TyConAppCo tc cos)   = tc `seq` seqCoArgs cos
seqCo (AppCo co1 co2)       = seqCo co1 `seq` seqCoArg co2
seqCo (ForAllCo cobndr co)  = seqCoBndr cobndr `seq` seqCo co
seqCo (CoVarCo cv)          = cv `seq` ()
seqCo (AxiomInstCo con ind cos) = con `seq` ind `seq` seqCos cos
seqCo (UnsafeCo ty1 ty2)    = seqType ty1 `seq` seqType ty2
seqCo (SymCo co)            = seqCo co
seqCo (TransCo co1 co2)     = seqCo co1 `seq` seqCo co2
seqCo (NthCo _ co)          = seqCo co
seqCo (LRCo _ co)           = seqCo co
seqCo (InstCo co arg)       = seqCo co `seq` seqCoArg ty
seqCo (CoherenceCo co1 co2) = seqCo co1 `seq` seqCo co2
seqCo (KindCo co)           = seqCo co

seqCos :: [Coercion] -> ()
seqCos []       = ()
seqCos (co:cos) = seqCo co `seq` seqCos cos

seqCoArg :: CoercionArg -> ()
seqCoArg (TyCoArg co)      = seqCo co
seqCoArg (CoCoArg co1 co2) = seqCo co1 `seq` seqCo co2

seqCoArgs :: [CoercionArg] -> ()
seqCoArgs []         = ()
seqCoArgs (arg:args) = seqCoArg arg `seq` seqCoArgs args
\end{code}


%************************************************************************
%*									*
	     The kind of a type, and of a coercion
%*									*
%************************************************************************

\begin{code}
coercionType :: Coercion -> Type
coercionType co = mkCoercionType ty1 ty2
  where Pair ty1 ty2 = coercionKind co

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
    go (TyConAppCo tc cos)  = mkTyConApp tc <$> (sequenceA $ map go_arg cos)
    go (AppCo co1 co2)      = mkAppTy <$> go co1 <*> go_arg co2
    go (ForAllCo (TyHomo tv) co)            = mkForAllTy tv <$> go co
    go (ForAllCo (TyHetero _ tv1 tv2 _) co) = mkForAllTy <$> Pair tv1 tv2 <*> go co
    go (ForAllCo (CoHomo tv) co)            = mkForAllTy tv <$> go co
    go (ForAllCo (CoHetero cv1 cv2) co)     = mkForAllTy <$> Pair cv1 cv2 <*> go co
    go (CoVarCo cv)         = toPair $ coVarTypes cv
    go (AxiomInstCo ax ind cos)
      = let branch         = coAxiomNthBranch ax ind
            tvs            = coAxBranchTyCoVars branch
            tys_pair       = sequenceA $ map go_arg cos 
        in substTyWith tvs <$> tys_pair <*> Pair (coAxNthLHS ax ind)
                                                 (coAxBranchRHS branch)
        <*> sequenceA (map go cos2)
    go (UnsafeCo ty1 ty2)   = Pair ty1 ty2
    go (SymCo co)           = swap $ go co
    go (TransCo co1 co2)    = Pair (pFst $ go co1) (pSnd $ go co2)
    go (NthCo d co)         = tyConAppArgN d <$> go co
    go (LRCo lr co)         = (pickLR lr . splitAppTy) <$> go co
    go (InstCo aco arg)     = go_app aco [arg]

    go_app :: Coercion -> [CoercionArg] -> Pair Type
    -- Collect up all the arguments and apply all at once
    -- See Note [Nested InstCos]
    go_app (InstCo co arg) args = go_app co (arg:args)
    go_app co              args = applyTys <$> go co <*> (sequenceA $ map co_arg args)

    go_arg :: CoercionArg -> Pair Type
    go_arg (TyCoArg co)      = go co
    go_arg (CoCoArg co1 co2) = Pair (CoercionTy co1) (CoercionTy co2)

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
