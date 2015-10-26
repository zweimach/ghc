-- (c) The University of Glasgow 2006

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}

module Unify (
        tcMatchTy, tcMatchTys, tcMatchTyX, tcMatchTysX, tcUnifyTyWithTFs,
        ruleMatchTyX,

        typesCantMatch,

        -- Side-effect free unification
        tcUnifyTy, tcUnifyTys,
        tcUnifyTysFG,
        BindFlag(..),
        UnifyResult, UnifyResultM(..),

        -- Matching a type against a lifted type (coercion)
        liftCoMatch
   ) where

#include "HsVersions.h"

import Var
import VarEnv
import VarSet
import Kind
import Type hiding ( getTvSubstEnv )
import Coercion
import TyCon
import TyCoRep hiding ( getTvSubstEnv, getCvSubstEnv )
import Util
import Pair

import Control.Monad
import Maybes
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ( Applicative(..) )
import Data.Traversable    ( traverse )
#endif
import Control.Applicative ( Alternative(..), (<$>) )

{-

Unification is much tricker than you might think.

1. The substitution we generate binds the *template type variables*
   which are given to us explicitly.

2. We want to match in the presence of foralls;
        e.g     (forall a. t1) ~ (forall b. t2)

   That is what the RnEnv2 is for; it does the alpha-renaming
   that makes it as if a and b were the same variable.
   Initialising the RnEnv2, so that it can generate a fresh
   binder when necessary, entails knowing the free variables of
   both types.

3. We must be careful not to bind a template type variable to a
   locally bound variable.  E.g.
        (forall a. x) ~ (forall b. b)
   where x is the template type variable.  Then we do not want to
   bind x to a/b!  This is a kind of occurs check.
   The necessary locals accumulate in the RnEnv2.

Note [Lazy coercions in Unify]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
After the internal matching algorithm is done running, we use
buildCoherenceCo to create a coercion between the input and the output.

This operation should always succeed after a successful match. But,
many times, we just care if the match succeeded or not. (That is,
many calls to tcMatchTy are wrapped in `isJust`). We don't want to
build the coercion at all in this case. So, we're careful to be lazy
in the return value from buildCoherenceCo.

Note [Kind coercions in Unify]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We wish to match/unify while ignoring casts. But, we can't just ignore
them completely, or we'll end up with ill-kinded substitutions. For example,
say we're matching `a` with `ty |> co`. If we just drop the cast, we'll
return [a |-> ty], but `a` and `ty` might have different kinds. We can't
just match/unify their kinds, either, because this might gratuitously
fail. After all, `co` is the witness that the kinds are the same -- they
may look nothing alike.

So, we pass a kind coercion to the match/unify worker. This coercion witnesses
the equality between the substed kind of the left-hand type and the substed
kind of the right-hand type. To get this coercion, we first have to match/unify
the kinds before looking at the types. Happily, we need look only one level
up, as all kinds are guaranteed to have kind *.

-}

-- | @tcMatchTy tys t1 t2@ produces a substitution (over a subset of
-- the variables @tys@) @s@ such that @s(t1)@ equals @t2@, as witnessed
-- by the returned coercion. That coercion will be reflexive whenever the
-- kinds of @s(t1)@ and @t2) are the same. Note that the returned substitution
-- never binds coercion variables. Returned coercion is nominal.
tcMatchTy :: TyCoVarSet -> Type -> Type -> Maybe (TCvSubst, Coercion)
tcMatchTy tmpls ty1 ty2
    -- See Note [Lazy coercions in Unify]
  = do { (subst, ~[co]) <- tcMatchTys tmpls [ty1] [ty2]
       ; return (subst, co) }

-- | This is similar to 'tcMatchTy', but extends a substitution
tcMatchTyX :: TyCoVarSet          -- ^ Template tyvars
           -> TCvSubst            -- ^ Substitution to extend
           -> Type                -- ^ Template
           -> Type                -- ^ Target
           -> Maybe (TCvSubst, Coercion)
tcMatchTyX tmpls subst ty1 ty2
    -- See Note [Lazy coercions in Unify]
  = do { (subst, ~[co]) <- tcMatchTysX tmpls subst [ty1] [ty2]
       ; return (subst, co) }

-- | Like 'tcMatchTy' but over a list of types.
tcMatchTys :: TyCoVarSet     -- ^ Template tyvars
           -> [Type]         -- ^ Template
           -> [Type]         -- ^ Target
           -> Maybe (TCvSubst, [Coercion])
                             -- ^ One-shot; in principle the template
                             -- variables could be free in the target
tcMatchTys tmpls tys1 tys2
  = tcMatchTysX tmpls (mkEmptyTCvSubst in_scope) tys1 tys2
  where
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOfTypes tys2)
        -- We're assuming that all the interesting
        -- tyvars in tys1 are in tmpls

-- | Like 'tcMatchTys', but extending a substitution
tcMatchTysX :: TyCoVarSet     -- ^ Template tyvars
            -> TCvSubst       -- ^ Substitution to extend
            -> [Type]         -- ^ Template
            -> [Type]         -- ^ Target
            -> Maybe (TCvSubst, [Coercion])  -- ^ One-shot substitution
tcMatchTysX tmpls (TCvSubst in_scope tv_env cv_env) tys1 tys2
-- See Note [Kind coercions in Unify]
  = case tc_unify_tys (matchBindFun tmpls) False
                      (mkRnEnv2 in_scope) tv_env tys1 tys2 of
      Unifiable tv_env' -> let subst = TCvSubst in_scope tv_env' cv_env in
                                  -- See Note [Lazy coercions in Unify]
                           Just (subst, map (expectJust "tcMatchTysX types") $
                                        zipWith buildCoherenceCo
                                                (substTys subst tys1) tys2)
      _                 -> Nothing

  where
    kis1 = map typeKind tys1
    kis2 = map typeKind tys2

-- | This one is called from the expression matcher,
-- which already has a MatchEnv in hand
ruleMatchTyX
  :: TyCoVarSet          -- ^ template variables
  -> RnEnv2
  -> TvSubstEnv          -- ^ type substitution to extend
  -> Type                -- ^ Template
  -> Type                -- ^ Target
  -> Maybe TvSubstEnv
ruleMatchTyX tmpl_tvs rn_env tenv tmpl target
-- See Note [Kind coercions in Unify]
  = case tc_unify_tys (matchBindFun tmpl_tvs) False rn_env
                      tenv [tmpl] [target] of
      Unifiable tenv' | let subst = mkOpenTCvSubst tenv' cenv
                      , substTy subst tmpl `eqType` target  -- we want exact matching here
                     -> Just tenv'
      _              -> Nothing
     -- TODO (RAE): This should probably work with inexact matching too;
     -- otherwise, various rules won't fire when they should

matchBindFun :: TyCoVarSet -> TyVar -> BindFlag
matchBindFun tvs tv = if tv `elemVarSet` tvs then BindMe else Skolem

{-
************************************************************************
*                                                                      *
                GADTs
*                                                                      *
************************************************************************

Note [Pruning dead case alternatives]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider        data T a where
                   T1 :: T Int
                   T2 :: T a

                newtype X = MkX Int
                newtype Y = MkY Char

                type family F a
                type instance F Bool = Int

Now consider    case x of { T1 -> e1; T2 -> e2 }

The question before the house is this: if I know something about the type
of x, can I prune away the T1 alternative?

Suppose x::T Char.  It's impossible to construct a (T Char) using T1,
        Answer = YES we can prune the T1 branch (clearly)

Suppose x::T (F a), where 'a' is in scope.  Then 'a' might be instantiated
to 'Bool', in which case x::T Int, so
        ANSWER = NO (clearly)

We see here that we want precisely the apartness check implemented within
tcUnifyTysFG. So that's what we do! Two types cannot match if they are surely
apart. Note that since we are simply dropping dead code, a conservative test
suffices.
-}

-- | Given a list of pairs of types, are any two members of a pair surely
-- apart, even after arbitrary type function evaluation and substitution?
typesCantMatch :: [(Type,Type)] -> Bool
-- See Note [Pruning dead case alternatives]
typesCantMatch prs = any (uncurry cant_match) prs
  where
    cant_match :: Type -> Type -> Bool
    cant_match t1 t2 = case tcUnifyTysFG (const BindMe) [t1] [t2] of
      SurelyApart -> True
      _           -> False

{-
************************************************************************
*                                                                      *
             Unification
*                                                                      *
************************************************************************

Note [Fine-grained unification]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Do the types (x, x) and ([y], y) unify? The answer is seemingly "no" --
no substitution to finite types makes these match. But, a substitution to
*infinite* types can unify these two types: [x |-> [[[...]]], y |-> [[[...]]] ].
Why do we care? Consider these two type family instances:

type instance F x x   = Int
type instance F [y] y = Bool

If we also have

type instance Looper = [Looper]

then the instances potentially overlap. The solution is to use unification
over infinite terms. This is possible (see [1] for lots of gory details), but
a full algorithm is a little more power than we need. Instead, we make a
conservative approximation and just omit the occurs check.

[1]: http://research.microsoft.com/en-us/um/people/simonpj/papers/ext-f/axioms-extended.pdf

tcUnifyTys considers an occurs-check problem as the same as general unification
failure.

tcUnifyTysFG ("fine-grained") returns one of three results: success, occurs-check
failure ("MaybeApart"), or general failure ("SurelyApart").

See also Trac #8162.

It's worth noting that unification in the presence of infinite types is not
complete. This means that, sometimes, a closed type family does not reduce
when it should. See test case indexed-types/should_fail/Overlap15 for an
example.

Note [The substitution in MaybeApart]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The constructor MaybeApart carries data with it, typically a TvSubstEnv. Why?
Because consider unifying these:

(a, a, Int) ~ (b, [b], Bool)

If we go left-to-right, we start with [a |-> b]. Then, on the middle terms, we
apply the subst we have so far and discover that we need [b |-> [b]]. Because
this fails the occurs check, we say that the types are MaybeApart (see above
Note [Fine-grained unification]). But, we can't stop there! Because if we
continue, we discover that Int is SurelyApart from Bool, and therefore the
types are apart. This has practical consequences for the ability for closed
type family applications to reduce. See test case
indexed-types/should_compile/Overlap14.

Note [Unifying with skolems]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we discover that two types unify if and only if a skolem variable is
substituted, we can't properly unify the types. But, that skolem variable
may later be instantiated with a unifyable type. So, we return maybeApart
in these cases.

Note [Lists of different lengths are MaybeApart]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It is unusual to call tcUnifyTys or tcUnifyTysFG with lists of different
lengths. The place where we know this can happen is from compatibleBranches in
FamInstEnv, when checking data family instances. Data family instances may be
eta-reduced; see Note [Eta reduction for data family axioms] in TcInstDcls.

We wish to say that

  D :: * -> * -> *
  axDF1 :: D Int ~ DFInst1
  axDF2 :: D Int Bool ~ DFInst2

overlap. If we conclude that lists of different lengths are SurelyApart, then
it will look like these do *not* overlap, causing disaster. See Trac #9371.

In usages of tcUnifyTys outside of family instances, we always use tcUnifyTys,
which can't tell the difference between MaybeApart and SurelyApart, so those
usages won't notice this design choice.
-}

-- always returns a nominal coercion
tcUnifyTy :: Type -> Type       -- All tyvars are bindable
          -> Maybe (TCvSubst, Coercion)
                       -- A regular one-shot (idempotent) substitution
-- Simple unification of two types; all type variables are bindable
tcUnifyTy t1 t2
   -- See Note [Lazy coercions in Unify]
  = do { (subst, ~[co]) <- tcUnifyTys (const BindMe) [t1] [t2]
       ; return (subst, co) }

-- | Unify two types, treating type family applications as possibly unifying
-- with anything and looking through injective type family applications.
tcUnifyTyWithTFs :: Bool  -- ^ True <=> do two-way unification;
                          --   False <=> do one-way matching.
                          --   See end of sec 5.2 from the paper
                 -> Type -> Type -> Maybe TCvSubst
-- This algorithm is a direct implementation of the "Algorithm U" presented in
-- the paper "Injective type families for Haskell", Figures 2 and 3.  Equation
-- numbers in the comments refer to equations from the paper.
-- TODO (RAE): Update this comment.
tcUnifyTyWithTFs twoWay t1 t2
  = case tc_unify_tys (const BindMe) twoWay rn_env emptyTvSubstEnv
                         [t1] [t2] of
      Unifiable  subst -> Just $ niFixTCvSubst subst
      MaybeApart subst -> Just $ niFixTCvSubst subst
      -- we want to *succeed* in questionable cases. This is a
      -- *pre-unification* algorithm.
      SurelyApart      -> Nothing
  where
    rn_env = mkRnEnv2 $ mkInScopeSet $ tyCoVarsOfTypes [t1, t2]

-----------------
tcUnifyTys :: (TyCoVar -> BindFlag)
           -> [Type] -> [Type]
           -> Maybe (TCvSubst, [Coercion])
                                -- ^ A regular one-shot (idempotent) substitution
                                -- that unifies the erased types. See comments
                                -- for 'tcUnifyTysFG'

-- The two types may have common type variables, and indeed do so in the
-- second call to tcUnifyTys in FunDeps.checkClsFD
tcUnifyTys bind_fn tys1 tys2
  = case tcUnifyTysFG bind_fn tys1 tys2 of
      Unifiable result -> Just result
      _                -> Nothing

-- This type does double-duty. It is used in the UM (unifier monad) and to
-- return the final result. See Note [Fine-grained unification]
type UnifyResult = UnifyResultM (TCvSubst, [Coercion])
data UnifyResultM a = Unifiable a        -- the subst that unifies the types
                    | MaybeApart a       -- the subst has as much as we know
                                         -- it must be part of an most general unifier
                                         -- See Note [The substitution in MaybeApart]
                    | SurelyApart
                    deriving Functor

instance Applicative UnifyResultM where
  pure  = Unifiable
  (<*>) = ap

instance Monad UnifyResultM where
  return = pure

  SurelyApart  >>= _ = SurelyApart
  MaybeApart x >>= f = case f x of
                         Unifiable y -> MaybeApart y
                         other       -> other
  Unifiable x  >>= f = f x

instance Alternative UnifyResultM where
  empty = SurelyApart

  a@(Unifiable {})  <|> _                 = a
  _                 <|> b@(Unifiable {})  = b
  a@(MaybeApart {}) <|> _                 = a
  _                 <|> b@(MaybeApart {}) = b
  SurelyApart       <|> SurelyApart       = SurelyApart

instance MonadPlus UnifyResultM where
  mzero = empty
  mplus = (<|>)

-- | @tcUnifyTysFG bind_tv tys1 tys2@ attepts to find a substitution @s@ (whose
-- domain elements all respond 'BindMe' to @bind_tv@) such that
-- @s(tys1)@ and that of @s(tys2)@ are equal, as witnessed by the returned
-- Coercions.
tcUnifyTysFG :: (TyVar -> BindFlag)
             -> [Type] -> [Type]
             -> UnifyResult
tcUnifyTysFG bind_fn tys1 tys2
  = do { env <- tc_unify_tys bind_fn True env emptyTvSubstEnv tys1 tys2
       ; let subst = niFixTCvSubst env
       ; return (subst, map (expectJust "tcUnifyTysFG") $
                        zipWith buildCoherenceCo
                                (substTys subst tys1)
                                (substTys subst tys2)) }
  where
    vars = tyCoVarsOfTypes tys1 `unionVarSet` tyCoVarsOfTypes tys2
    env  = mkRnEnv2 $ mkInScopeSet vars

-- | This function is actually the one to call the unifier -- a little
-- too general for outside clients, though.
tc_unify_tys :: (TyVar -> BindFlag)
             -> Bool        -- ^ True <=> unify; False <=> match
             -> RnEnv2
             -> TvSubstEnv  -- ^ substitution to extend
             -> [Type] -> [Type]
             -> UnifyResultM TvSubstEnv
tc_unify_tys bind_fn unif rn_env tv_env tys1 tys2
  = initUM bind_fn unif rn_env tv_env $
    do { unify_tys kis1 kis2
       ; unify_tys tys1 tys2
       ; getTvSubstEnv }
  where
    kis1 = map typeKind tys1
    kis2 = map typeKind tys2

{-
************************************************************************
*                                                                      *
                Non-idempotent substitution
*                                                                      *
************************************************************************

Note [Non-idempotent substitution]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
During unification we use a TvSubstEnv/CvSubstEnv pair that is
  (a) non-idempotent
  (b) loop-free; ie repeatedly applying it yields a fixed point

Note [Finding the substitution fixpoint]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Finding the fixpoint of a non-idempotent substitution arising from a
unification is harder than it looks, because of kinds.  Consider
   T k (H k (f:k)) ~ T * (g:*)
If we unify, we get the substitution
   [ k -> *
   , g -> H k (f:k) ]
To make it idempotent we don't want to get just
   [ k -> *
   , g -> H * (f:k) ]
We also want to substitute inside f's kind, to get
   [ k -> *
   , g -> H k (f:*) ]
If we don't do this, we may apply the substitition to something,
and get an ill-formed type, i.e. one where typeKind will fail.
This happened, for example, in Trac #9106.

This is the reason for extending env with [f:k -> f:*], in the
definition of env' in niFixTvSubst
-}

niFixTCvSubst :: TvSubstEnv -> TCvSubst
-- Find the idempotent fixed point of the non-idempotent substitution
-- See Note [Finding the substitution fixpoint]
-- ToDo: use laziness instead of iteration?
niFixTCvSubst tenv = f tenv
  where
    f tenv
        | not_fixpoint = f (mapVarEnv (substTy subst') tenv)
        | otherwise    = subst
        where
          not_fixpoint  = foldVarSet ((||) . in_domain) False range_tvs
          in_domain tv  = tv `elemVarEnv` tenv

          range_tvs     = foldVarEnv (unionVarSet . tyCoVarsOfType) emptyVarSet tenv
          subst         = mkTCvSubst (mkInScopeSet range_tvs)
                                     (tenv, emptyCvSubstEnv)

             -- env' extends env by replacing any free type with
             -- that same tyvar with a substituted kind
             -- See note [Finding the substitution fixpoint]
          tenv'         = extendVarEnvList tenv [ (rtv, mkTyVarTy $
                                                        setTyVarKind rtv $
                                                        substTy subst $
                                                        tyVarKind rtv)
                                                | rtv <- varSetElems range_tvs
                                                , not (in_domain rtv) ]
          subst'        = mkTCvSubst (mkInScopeSet range_tvs)
                                     (tenv', emptyCvSubstEnv)

niSubstTvSet :: TvSubstEnv -> TyCoVarSet -> TyCoVarSet
-- Apply the non-idempotent substitution to a set of type variables,
-- remembering that the substitution isn't necessarily idempotent
-- This is used in the occurs check, before extending the substitution
niSubstTvSet tsubst tvs
  = foldVarSet (unionVarSet . get) emptyVarSet tvs
  where
    get tv
      | Just ty <- lookupVarEnv tsubst tv
      = niSubstTvSet tsubst (tyCoVarsOfType ty)

      | otherwise
      = unitVarSet tv

{-
************************************************************************
*                                                                      *
                The workhorse
*                                                                      *
************************************************************************

-}

unify_ty :: Type -> Type -> Coercion   -- Types to be unified and a co
                                       -- between their kinds
                                       -- See Note [Kind coercions in Unify]
         -> UM ()
-- Respects newtypes, PredTypes

unify_ty ty1 ty2 kco
  | Just ty1' <- tcView ty1 = unify_ty ty1' ty2 kco
  | Just ty2' <- tcView ty2 = unify_ty ty1 ty2' kco
  | CastTy ty1' co <- ty1                = unify_ty ty1' ty2 (co `mkTransCo` kco)
  | CastTy ty2' co <- ty2                = unify_ty ty1 ty2'
                                                    (kco `mkTransCo` mkSymCo co)

-- Respects newtypes, PredTypes

unify_ty (TyVarTy tv1) ty2 kco = uVar tv1 ty2 kco
unify_ty ty1 (TyVarTy tv2) kco
  = do { unif <- amIUnifying
       ; if unif
         then umSwapRn $ uVar tv2 ty1 (mkSymCo kco)
         else surelyApart }  -- non-tv on left; tv on right: can't match.

unify_ty ty1 ty2
  | Just (tc1, tys1) <- splitTyConApp_maybe ty1
  , Just (tc2, tys2) <- splitTyConApp_maybe ty2
  = if tc1 == tc2 || (isStarKind ty1 && isStarKind ty2)
    then if isInjectiveTyCon tc1 Nominal
         then unify_tys tys1 tys2
         else let inj | isTypeFamilyTyCon tc1
                      = case familyTyConInjectivityInfo tc1 of
                          NotInjective -> repeat False
                          Injective bs -> bs
                      | otherwise
                      = repeat False

                  inj_tys1 = filterByList inj tys1
                  inj_tys2 = filterByList inj tys2
              in
              don'tBeSoSure $ unify_tys inj_tys1 inj_tys2
    else -- tc1 /= tc2
         if isGenerativeTyCon tc1 Nominal && isGenerativeTyCon tc2 Nominal
         then surelyApart
         else maybeApart

        -- Applications need a bit of care!
        -- They can match FunTy and TyConApp, so use splitAppTy_maybe
        -- NB: we've already dealt with type variables,
        -- so if one type is an App the other one jolly well better be too
unify_ty (AppTy ty1a ty1b) ty2 _kco
  | Just (ty2a, ty2b) <- repSplitAppTy_maybe ty2
  = unify_ty_app ty1a ty1b ty2a ty2b

unify_ty ty1 (AppTy ty2a ty2b) _kco
  | Just (ty1a, ty1b) <- repSplitAppTy_maybe ty1
  = unify_ty_app ty1a ty1b ty2a ty2b

unify_ty (LitTy x) (LitTy y) _kco | x == y = return ()

unify_ty (ForAllTy (Named tv1 _) ty1) (ForAllTy (Named tv2 _) ty2) kco
  = do { unify_ty (tyVarKind tv1) (tyVarKind tv2) (mkNomReflCo liftedTypeKind)
       ; umRnBndr2 tv1 tv2 $ unify_ty ty1 ty2 kco }

unify_ty (CoercionTy {}) (CoercionTy {}) _kco = return ()

unify_ty ty1 _ _
  | Just (tc1, _) <- splitTyConApp_maybe ty1
  , not (isGenerativeTyCon tc1 Nominal)
  = maybeApart

unify_ty _ ty2 _
  | Just (tc2, _) <- splitTyConApp_maybe ty2
  , not (isGenerativeTyCon tc2 Nominal)
  = do { unif <- amIUnifying
       ; if unif then maybeApart else surelyApart }

unify_ty _ _ _ = surelyApart

unify_ty_app :: Type -> Type -> Type -> Type -> UM ()
unify_ty_app ty1a ty1b ty2a ty2b
  = do { -- TODO (RAE): Remove this exponential behavior.
         let ki1a = typeKind ty1a
             ki2a = typeKind ty2a
       ; unify_ty ki1a ki2a (mkNomReflCo liftedTypeKind)
       ; let kind_co = mkNomReflCo ki1a
       ; unify_ty ty1a ty2a kind_co
       ; unify_ty ty1b ty2b (mkNthCo 0 kind_co) }

unify_tys :: [Type] -> [Type] -> UM ()
unify_tys orig_xs orig_ys
  = go orig_xs orig_ys
  where
    go []     []     = return ()
    go (x:xs) (y:ys)
      = do { unify_ty x y (mkNomReflCo $ typeKind x)
           ; go xs ys }
    go _ _ = maybeApart  -- See Note [Lists of different lengths are MaybeApart]

---------------------------------
uVar :: TyVar           -- Variable to be unified
     -> Type            -- with this Type
     -> Coercion        -- :: kind tv ~N kind ty
     -> UM ()

uVar tv1 ty kco
 = do { -- Check to see whether tv1 is refined by the substitution
        subst <- getTvSubstEnv
      ; case (lookupVarEnv subst tv1) of
          Just ty' -> unify_ty ty' ty kco        -- Yes, call back into unify
          Nothing  -> uUnrefined tv1 ty ty kco } -- No, continue

uUnrefined :: TyVar             -- variable to be unified
           -> Type              -- with this Type
           -> Type              -- (version w/ expanded synonyms)
           -> Coercion          -- :: kind tv ~N kind ty
           -> UM ()

-- We know that tv1 isn't refined

uUnrefined tv1 ty2 ty2' kco
  | Just ty2'' <- tcView ty2'
  = uUnrefined tv1 ty2 ty2'' kco    -- Unwrap synonyms
                -- This is essential, in case we have
                --      type Foo a = a
                -- and then unify a ~ Foo a

  | TyVarTy tv2 <- ty2'
  = do { tv1' <- umRnOccL tv1
       ; tv2' <- umRnOccR tv2
       ; when (tv1' /= tv2') $ do -- when they are equal, success: do nothing
       { subst <- getTvSubstEnv
          -- Check to see whether tv2 is refined
       ; case lookupVarEnv subst tv2 of
         {  Just ty' -> uUnrefined tv1 ty' ty' kco
         ;  Nothing  -> do
       {   -- So both are unrefined

           -- And then bind one or the other,
           -- depending on which is bindable
       ; b1 <- tvBindFlag tv1
       ; b2 <- tvBindFlag tv2
       ; unif <- amIUnifying
       ; let ty1 = mkTyVarTy tv1
       ; case (b1, b2) of
           (BindMe, _)        -> do { checkRnEnvR ty2 -- make sure ty2 is not a local
                                    ; extendTvEnv tv1 (ty2 `mkCastTy` kco) }
           (_, BindMe) | unif -> do { checkRnEnvL ty1 -- ditto for ty1
                                    ; extendTvEnv tv2 (ty1 `mkCastTy` mkSymCo kco) }
           _ -> maybeApart -- See Note [Unification with skolems]
  }}}}

uUnrefined tv1 ty2 ty2' kco -- ty2 is not a type variable
  = do { occurs <- elemNiSubstSet tv1 (tyCoVarsOfType ty2')
       ; if occurs
         then maybeApart       -- Occurs check, see Note [Fine-grained unification]
         else do bindTv tv1 (ty2 `mkCastTy` mkSymCo kco) }
            -- Bind tyvar to the synonym if poss

elemNiSubstSet :: TyVar -> TyCoVarSet -> UM Bool
elemNiSubstSet v set
  = do { tsubst <- getTvSubstEnv
       ; return $ v `elemVarSet` niSubstTvSet tsubst set }

bindTv :: TyVar -> Type -> UM ()
bindTv tv ty    -- ty is not a variable
  = do  { checkRnEnvR ty -- make sure ty mentions no local variables
        ; b <- tvBindFlag tv
        ; case b of
            Skolem -> maybeApart  -- See Note [Unification with skolems]
            BindMe -> extendTvEnv tv ty
        }

{-
%************************************************************************
%*                                                                      *
                Binding decisions
*                                                                      *
************************************************************************
-}

data BindFlag
  = BindMe      -- A regular type variable

  | Skolem      -- This type variable is a skolem constant
                -- Don't bind it; it only matches itself

{-
************************************************************************
*                                                                      *
                Unification monad
*                                                                      *
************************************************************************
-}

newtype UM a = UM { unUM :: (TyVar -> BindFlag) -- the user-supplied BingFlag function
                         -> Bool                -- unification (True) or matching?
                         -> RnEnv2              -- the renaming env for local variables
                         -> TyCoVarSet          -- set of all local variables
                         -> TvSubstEnv          -- substitutions
                         -> UnifyResultM (TvSubstEnv, a) }

instance Functor UM where
      fmap = liftM

instance Applicative UM where
      pure a = UM (\_ _ _ _ tsubst -> pure (tsubst, a))
      (<*>)  = ap

instance Monad UM where
  return   = pure
  fail _   = UM (\_ _ _ _ _ -> SurelyApart) -- failed pattern match
  m >>= k  = UM (\tvs unif rn_env locals tsubst ->
                  do { (tsubst', v) <- unUM m tvs unif rn_env locals tsubst
                     ; unUM (k v) tvs unif rn_env locals tsubst' })

instance Alternative UM where
  empty     = UM (\_ _ _ _ _ -> mzero)
  m1 <|> m2 = UM (\tvs unif rn_env locals tsubst ->
                  unUM m1 tvs unif rn_env locals tsubst <|>
                  unUM m2 tvs unif rn_env locals tsubst)

  -- need this instance because of a use of 'guard' above
instance MonadPlus UM where
  mzero = empty
  mplus = (<|>)

initUM :: (TyVar -> BindFlag)
       -> Bool        -- True <=> unify; False <=> match
       -> RnEnv2
       -> TvSubstEnv  -- subst to extend
       -> UM a -> UnifyResultM a
initUM badtvs unif rn_env subst_env um
  = case unUM um badtvs unif rn_env emptyVarSet subst_env of
      Unifiable (_, subst)  -> Unifiable subst
      MaybeApart (_, subst) -> MaybeApart subst
      SurelyApart           -> SurelyApart

tvBindFlag :: TyVar -> UM BindFlag
tvBindFlag tv = UM $ \tv_fn _ _ locals tsubst ->
  Unifiable (tsubst, if tv `elemVarSet` locals then Skolem else tv_fn tv)

getTvSubstEnv :: UM TvSubstEnv
getTvSubstEnv = UM $ \_ _ _ _ tsubst -> Unifiable (tsubst, tsubst)

getTCvSubst :: UM TCvSubst
getTCvSubst = UM $ \_ _ _ _ tsubst -> Unifiable (tsubst, niFixTCvSubst tsubst)

extendTvEnv :: TyVar -> Type -> UM ()
extendTvEnv tv ty = UM $ \_ _ _ _ tsubst ->
  Unifiable (extendVarEnv tsubst tv ty, ())

umRnBndr2 :: TyCoVar -> TyCoVar -> UM a -> UM a
umRnBndr2 v1 v2 thing = UM $ \tv_fn unif rn_env locals tsubst ->
  let (rn_env', v3) = rnBndr2_var rn_env v1 v2
      locals'       = extendVarSetList locals [v1, v2, v3]
  in unUM thing tv_fn unif rn_env' locals' tsubst

checkRnEnv :: (RnEnv2 -> Var -> Bool) -> Type -> UM ()
checkRnEnv inRnEnv ty = UM $ \_ _ rn_env _ tsubst ->
  let varset = tyCoVarsOfType ty in
  if any (inRnEnv rn_env) (varSetElems varset)
  then MaybeApart (tsubst, ())
  else Unifiable (tsubst, ())

-- | Converts any SurelyApart to a MaybeApart
don'tBeSoSure :: UM () -> UM ()
don'tBeSoSure um = UM $ \tv_fn unif rn_env locals tsubst ->
  case unUM um tv_fn unif rn_env locals tsubst of
    SurelyApart -> MaybeApart (tsubst, ())
    other       -> other

checkRnEnvR :: Type -> UM ()
checkRnEnvR = checkRnEnv inRnEnvR

checkRnEnvL :: Type -> UM ()
checkRnEnvL = checkRnEnv inRnEnvL

umRnOccL :: TyVar -> UM TyVar
umRnOccL v = UM $ \_ _ rn_env _ tsubst ->
  Unifiable (tsubst, rnOccL rn_env v)

umRnOccR :: TyVar -> UM TyVar
umRnOccR v = UM $ \_ _ rn_env _ tsubst ->
  Unifiable (tsubst, rnOccR rn_env v)

umSwapRn :: UM a -> UM a
umSwapRn thing = UM $ \tv_fn unif rn_env locals tsubst ->
  let rn_env' = rnSwap rn_env in
  unUM thing tv_fn unif rn_env' locals tsubst

amIUnifying :: UM Bool
amIUnifying = UM $ \_ unif _ _ tsubst -> Unifiable (tsubst, unif)

maybeApart :: UM ()
maybeApart = UM (\_ _ _ _ tsubst -> MaybeApart (tsubst, ()))

surelyApart :: UM a
surelyApart = UM (\_ _ _ _ _ -> SurelyApart)

{-
%************************************************************************
%*                                                                      *
            Matching a (lifted) type against a coercion
%*                                                                      *
%************************************************************************

This section defines essentially an inverse to liftCoSubst. It is defined
here to avoid a dependency from Coercion on this module.

-}

-- | 'liftCoMatch' is sort of inverse to 'liftCoSubst'.  In particular, if
--   @liftCoMatch vars ty co == Just s@, then @tyCoSubst s ty == co@,
--   where @==@ there means that the result of tyCoSubst has the same
--   type as the original co; but may be different under the hood.
--   That is, it matches a type against a coercion of the same
--   "shape", and returns a lifting substitution which could have been
--   used to produce the given coercion from the given type.
--   Note that this function is incomplete -- it might return Nothing
--   when there does indeed exist a possible lifting context.
--
-- This function is incomplete in that it doesn't respect the equality
-- in `eqType`. That is, it's possible that this will succeed for t1 and
-- fail for t2, even when t1 `eqType` t2. That's because it depends on
-- there being a very similar structure between the type and the coercion.
-- This incompleteness shouldn't be all that surprising, especially because
-- it depends on the structure of the coercion, which is a silly thing to do.
--
-- The lifting context produced doesn't have to be exacting in the roles
-- of the mappings. This is because any use of the lifting context will
-- also require a desired role. Thus, this algorithm prefers mapping to
-- nominal coercions where it can do so.
liftCoMatch :: TyCoVarSet -> Type -> Coercion -> Maybe LiftingContext
liftCoMatch tmpls ty co
  = do { cenv1 <- ty_co_match menv emptyVarEnv ki ki_co ki_ki_co ki_ki_co
       ; cenv2 <- ty_co_match menv cenv1       ty co
                              (mkNomReflCo co_lkind) (mkNomReflCo co_rkind)
       ; return (LC (mkEmptyTCvSubst in_scope) cenv2) }
  where
    menv     = ME { me_tmpls = tmpls, me_env = mkRnEnv2 in_scope }
    in_scope = mkInScopeSet (tmpls `unionVarSet` tyCoVarsOfCo co)
    -- Like tcMatchTy, assume all the interesting variables
    -- in ty are in tmpls

    ki       = typeKind ty
    ki_co    = promoteCoercion co
    ki_ki_co = mkNomReflCo liftedTypeKind

    Pair co_lkind co_rkind = coercionKind ki_co

-- | 'ty_co_match' does all the actual work for 'liftCoMatch'.
ty_co_match :: MatchEnv   -- ^ ambient helpful info
            -> LiftCoEnv  -- ^ incoming subst
            -> Type       -- ^ ty, type to match
            -> Coercion   -- ^ co, coercion to match against
            -> Coercion   -- ^ :: kind of L type of substed ty ~N L kind of co
            -> Coercion   -- ^ :: kind of R type of substed ty ~N R kind of co
            -> Maybe LiftCoEnv
ty_co_match menv subst ty co lkco rkco
  | Just ty' <- coreViewOneStarKind ty = ty_co_match menv subst ty' co lkco rkco

  -- handle Refl case:
  | tyCoVarsOfType ty `isNotInDomainOf` subst
  , Just (ty', _) <- isReflCo_maybe co
  , Just _ <- buildCoherenceCoX (me_env menv) ty ty'
  = Just subst

  where
    isNotInDomainOf :: VarSet -> VarEnv a -> Bool
    isNotInDomainOf set env
      = noneSet (\v -> elemVarEnv v env) set

    noneSet :: (Var -> Bool) -> VarSet -> Bool
    noneSet f = foldVarSet (\v rest -> rest && (not $ f v)) True

ty_co_match menv subst ty co lkco rkco
  | CastTy ty' co' <- ty
  = ty_co_match menv subst ty' co (co' `mkTransCo` lkco) (co' `mkTransCo` rkco)

  | CoherenceCo co1 co2 <- co
  = ty_co_match menv subst ty co1 (lkco `mkTransCo` mkSymCo co2) rkco

  | SymCo co' <- co
  = swapLiftCoEnv <$> ty_co_match menv (swapLiftCoEnv subst) ty co' rkco lkco

  -- Match a type variable against a non-refl coercion
ty_co_match menv subst (TyVarTy tv1) co lkco rkco
  | Just co1' <- lookupVarEnv subst tv1' -- tv1' is already bound to co1
  = if eqCoercionX (nukeRnEnvL rn_env) co1' co
    then Just subst
    else Nothing       -- no match since tv1 matches two different coercions

  | tv1' `elemVarSet` me_tmpls menv           -- tv1' is a template var
  = if any (inRnEnvR rn_env) (varSetElems (tyCoVarsOfCo co))
    then Nothing      -- occurs check failed
    else Just $ extendVarEnv subst tv1' $
                castCoercionKind co (mkSymCo lkco) (mkSymCo rkco)

  | otherwise
  = Nothing

  where
    rn_env = me_env menv
    tv1' = rnOccL rn_env tv1

  -- just look through SubCo's. We don't really care about roles here.
ty_co_match menv subst ty (SubCo co) lkco rkco
  = ty_co_match menv subst ty co lkco rkco

ty_co_match menv subst (AppTy ty1a ty1b) co _lkco _rkco
  | Just (co2, arg2) <- splitAppCo_maybe co     -- c.f. Unify.match on AppTy
  = ty_co_match_app menv subst ty1a ty1b co2 arg2
ty_co_match menv subst ty1 (AppCo co2 arg2) _lkco _rkco
  | Just (ty1a, ty1b) <- repSplitAppTy_maybe ty1
  = ty_co_match_app menv subst ty1a ty1b co2 arg2

ty_co_match menv subst (TyConApp tc1 tys) (TyConAppCo _ tc2 cos) _lkco _rkco
  = ty_co_match_tc menv subst tc1 tys tc2 cos
ty_co_match menv subst (ForAllTy (Anon ty1) ty2) (TyConAppCo _ tc cos) _lkco _rkco
  = ty_co_match_tc menv subst funTyCon [ty1, ty2] tc cos

ty_co_match menv subst (ForAllTy (Named tv1 _) ty1)
                       (ForAllCo tv2 kind_co2 co2)
                       lkco rkco
  = do { subst1 <- ty_co_match menv subst (tyVarKind tv1) kind_co2
                               ki_ki_co ki_ki_co
       ; let rn_env0 = me_env menv
             rn_env1 = rnBndr2 rn_env0 tv1 tv2
             menv'   = menv { me_env = rn_env1 }
       ; ty_co_match menv' subst1 ty1 co2 lkco rkco }
  where
    ki_ki_co = mkNomReflCo liftedTypeKind

ty_co_match _ subst (CoercionTy {}) _ _ _
  = Just subst -- don't inspect coercions

ty_co_match menv subst ty co lkco rkco
  | Just co' <- pushRefl co = ty_co_match menv subst ty co' lkco rkco
  | otherwise               = Nothing

ty_co_match_tc :: MatchEnv -> LiftCoEnv
               -> TyCon -> [Type]
               -> TyCon -> [Coercion]
               -> Maybe LiftCoEnv
ty_co_match_tc menv subst tc1 tys1 tc2 cos2
  = do { guard (tc1 == tc2)
       ; ty_co_match_args menv subst tys1 cos2 lkcos rkcos }
  where
    Pair lkcos rkcos
      = traverse (fmap mkNomReflCo . coercionKind) cos2

ty_co_match_app :: MatchEnv -> LiftCoEnv
                -> Type -> Type -> Coercion -> Coercion
                -> Maybe LiftCoEnv
ty_co_match_app menv subst ty1a ty1b co2a co2b
  = do { -- TODO (RAE): Remove this exponential behavior.
         subst1 <- ty_co_match menv subst  ki1a ki2a ki_ki_co ki_ki_co
       ; let Pair lkco rkco = mkNomReflCo <$> coercionKind ki2a
       ; subst2 <- ty_co_match menv subst1 ty1a co2a lkco rkco
       ; ty_co_match menv subst2 ty1b co2b (mkNthCo 0 lkco) (mkNthCo 0 rkco) }
  where
    ki1a = typeKind ty1a
    ki2a = promoteCoercion co2a
    ki_ki_co = mkNomReflCo liftedTypeKind

ty_co_match_args :: MatchEnv -> LiftCoEnv -> [Type]
                 -> [Coercion] -> [Coercion] -> [Coercion]
                 -> Maybe LiftCoEnv
ty_co_match_args _    subst []       []         _ _ = Just subst
ty_co_match_args menv subst (ty:tys) (arg:args) (lkco:lkcos) (rkco:rkcos)
  = do { subst' <- ty_co_match menv subst ty arg lkco rkco
       ; ty_co_match_args menv subst' tys args lkcos rkcos }
ty_co_match_args _    _     _        _          _ _ = Nothing

pushRefl :: Coercion -> Maybe Coercion
pushRefl (Refl Nominal (AppTy ty1 ty2))
  = Just (AppCo (Refl Nominal ty1) (mkNomReflCo ty2))
pushRefl (Refl r (ForAllTy (Anon ty1) ty2))
  = Just (TyConAppCo r funTyCon [mkReflCo r ty1, mkReflCo r ty2])
pushRefl (Refl r (TyConApp tc tys))
  = Just (TyConAppCo r tc (zipWith mkReflCo (tyConRolesX r tc) tys))
pushRefl (Refl r (ForAllTy (Named tv _) ty))
  = Just (mkHomoForAllCos_NoRefl [tv] (Refl r ty))
    -- NB: NoRefl variant. Otherwise, we get a loop!
pushRefl (Refl r (CastTy ty co))  = Just (castCoercionKind (Refl r ty) co co)
pushRefl _                        = Nothing
