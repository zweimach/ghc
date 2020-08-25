{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

-}

{-# LANGUAGE CPP, DeriveFunctor, MultiWayIf, TupleSections,
    ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns   #-}
{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

-- | Type subsumption and unification
module GHC.Tc.Utils.Unify (
  -- Full-blown subsumption
  tcWrapResult, tcWrapResultO, tcWrapResultMono,
  tcSkolemise, tcSkolemiseScoped, tcSkolemiseAlways, tcSkolemiseET,
  tcSubType, tcSubTypeSigma, tcSubTypePat,
  tcSubMult,
  checkConstraints, checkTvConstraints,
  buildImplicationFor, buildTvImplication, emitResidualTvConstraint,

  -- Various unifications
  unifyType, unifyKind,
  uType, promoteTcType,
  swapOverTyVars, canSolveByUnification,

  --------------------------------
  -- Holes
  tcInfer,
  matchExpectedListTy,
  matchExpectedTyConApp,
  matchExpectedAppTy,
  matchExpectedFunTys,
  matchExpectedFunKind,
  matchActualFunTySigma, matchActualFunTysRho,

  metaTyVarUpdateOK, occCheckForErrors, MetaTyVarUpdateResult(..)

  ) where

#include "HsVersions.h"

import GHC.Prelude

import GHC.Hs
import GHC.Core.TyCo.Rep
import GHC.Core.TyCo.Ppr( debugPprType )
import GHC.Tc.Utils.TcMType
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.TcType
import GHC.Tc.Utils.Env
import GHC.Core.Type
import GHC.Core.Coercion
import GHC.Core.Multiplicity
import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Constraint
import GHC.Core.Predicate
import GHC.Tc.Types.Origin
import GHC.Types.Name( isSystemName )
import GHC.Tc.Utils.Instantiate
import GHC.Core.TyCon
import GHC.Builtin.Types
import GHC.Types.Var as Var
import GHC.Types.Var.Set
import GHC.Types.Var.Env
import GHC.Utils.Error
import GHC.Driver.Session
import GHC.Types.Basic
import GHC.Data.Bag
import GHC.Utils.Misc
import GHC.Utils.Outputable as Outputable
import GHC.Utils.Panic

import Control.Monad
import Control.Arrow ( second )


{- *********************************************************************
*                                                                      *
              matchActualFunTys
*                                                                      *
********************************************************************* -}

-- | matchActualFunTySigma does looks for just one function arrow
--   returning an uninstantiated sigma-type
matchActualFunTySigma
  :: SDoc -- See Note [Herald for matchExpectedFunTys]
  -> Maybe SDoc                    -- The thing with type TcSigmaType
  -> (Arity, [Scaled TcSigmaType]) -- Total number of value args in the call, and
                                   -- types of values args to which function has
                                   --   been applied already (reversed)
                                   -- Both are used only for error messages)
  -> TcRhoType                     -- Type to analyse: a TcRhoType
  -> TcM (HsWrapper, Scaled TcSigmaType, TcSigmaType)
-- See Note [matchActualFunTy error handling] for the first three arguments

-- If   (wrap, arg_ty, res_ty) = matchActualFunTySigma ... fun_ty
-- then wrap :: fun_ty ~> (arg_ty -> res_ty)
-- and NB: res_ty is an (uninstantiated) SigmaType

matchActualFunTySigma herald mb_thing err_info fun_ty
  = go fun_ty
  where
    -- Does not allocate unnecessary meta variables: if the input already is
    -- a function, we just take it apart.  Not only is this efficient,
    -- it's important for higher rank: the argument might be of form
    --              (forall a. ty) -> other
    -- If allocated (fresh-meta-var1 -> fresh-meta-var2) and unified, we'd
    -- hide the forall inside a meta-variable
    go :: TcSigmaType   -- The remainder of the type as we're processing
       -> TcM (HsWrapper, Scaled TcSigmaType, TcSigmaType)
    go ty | Just ty' <- tcView ty = go ty'

    go (FunTy { ft_af = af, ft_mult = w, ft_arg = arg_ty, ft_res = res_ty })
      = ASSERT( af == VisArg )
        return (idHsWrapper, Scaled w arg_ty, res_ty)

    go ty@(TyVarTy tv)
      | isMetaTyVar tv
      = do { cts <- readMetaTyVar tv
           ; case cts of
               Indirect ty' -> go ty'
               Flexi        -> defer ty }

       -- In all other cases we bale out into ordinary unification
       -- However unlike the meta-tyvar case, we are sure that the
       -- number of arguments doesn't match arity of the original
       -- type, so we can add a bit more context to the error message
       -- (cf #7869).
       --
       -- It is not always an error, because specialized type may have
       -- different arity, for example:
       --
       -- > f1 = f2 'a'
       -- > f2 :: Monad m => m Bool
       -- > f2 = undefined
       --
       -- But in that case we add specialized type into error context
       -- anyway, because it may be useful. See also #9605.
    go ty = addErrCtxtM (mk_ctxt ty) (defer ty)

    ------------
    defer fun_ty
      = do { arg_ty <- newOpenFlexiTyVarTy
           ; res_ty <- newOpenFlexiTyVarTy
           ; let unif_fun_ty = mkVisFunTyMany arg_ty res_ty
           ; co <- unifyType mb_thing fun_ty unif_fun_ty
           ; return (mkWpCastN co, unrestricted arg_ty, res_ty) }

    ------------
    mk_ctxt :: TcType -> TidyEnv -> TcM (TidyEnv, MsgDoc)
    mk_ctxt res_ty env = mkFunTysMsg env herald (reverse arg_tys_so_far)
                                     res_ty n_val_args_in_call
    (n_val_args_in_call, arg_tys_so_far) = err_info

{- Note [matchActualFunTy error handling]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
matchActualFunTySigma is made much more complicated by the
desire to produce good error messages. Consider the application
    f @Int x y
In GHC.Tc.Gen.Expr.tcArgs we deal with visible type arguments,
and then call matchActualFunTysPart for each individual value
argument. It, in turn, must instantiate any type/dictionary args,
before looking for an arrow type.

But if it doesn't find an arrow type, it wants to generate a message
like "f is applied to two arguments but its type only has one".
To do that, it needs to konw about the args that tcArgs has already
munched up -- hence passing in n_val_args_in_call and arg_tys_so_far;
and hence also the accumulating so_far arg to 'go'.

This allows us (in mk_ctxt) to construct f's /instantiated/ type,
with just the values-arg arrows, which is what we really want
in the error message.

Ugh!
-}

-- Like 'matchExpectedFunTys', but used when you have an "actual" type,
-- for example in function application
matchActualFunTysRho :: SDoc   -- See Note [Herald for matchExpectedFunTys]
                     -> CtOrigin
                     -> Maybe SDoc  -- the thing with type TcSigmaType
                     -> Arity
                     -> TcSigmaType
                     -> TcM (HsWrapper, [Scaled TcSigmaType], TcRhoType)
-- If    matchActualFunTysRho n ty = (wrap, [t1,..,tn], res_ty)
-- then  wrap : ty ~> (t1 -> ... -> tn -> res_ty)
--       and res_ty is a RhoType
-- NB: the returned type is top-instantiated; it's a RhoType
matchActualFunTysRho herald ct_orig mb_thing n_val_args_wanted fun_ty
  = go n_val_args_wanted [] fun_ty
  where
    go n so_far fun_ty
      | not (isRhoTy fun_ty)
      = do { (wrap1, rho) <- topInstantiate ct_orig fun_ty
           ; (wrap2, arg_tys, res_ty) <- go n so_far rho
           ; return (wrap2 <.> wrap1, arg_tys, res_ty) }

    go 0 _ fun_ty = return (idHsWrapper, [], fun_ty)

    go n so_far fun_ty
      = do { (wrap_fun1, arg_ty1, res_ty1) <- matchActualFunTySigma
                                                 herald mb_thing
                                                 (n_val_args_wanted, so_far)
                                                 fun_ty
           ; (wrap_res, arg_tys, res_ty)   <- go (n-1) (arg_ty1:so_far) res_ty1
           ; let wrap_fun2 = mkWpFun idHsWrapper wrap_res arg_ty1 res_ty doc
           ; return (wrap_fun2 <.> wrap_fun1, arg_ty1:arg_tys, res_ty) }
      where
        doc = text "When inferring the argument type of a function with type" <+>
              quotes (ppr fun_ty)


{-
************************************************************************
*                                                                      *
             matchExpected functions
*                                                                      *
************************************************************************

Note [Herald for matchExpectedFunTys]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The 'herald' always looks like:
   "The equation(s) for 'f' have"
   "The abstraction (\x.e) takes"
   "The section (+ x) expects"
   "The function 'f' is applied to"

This is used to construct a message of form

   The abstraction `\Just 1 -> ...' takes two arguments
   but its type `Maybe a -> a' has only one

   The equation(s) for `f' have two arguments
   but its type `Maybe a -> a' has only one

   The section `(f 3)' requires 'f' to take two arguments
   but its type `Int -> Int' has only one

   The function 'f' is applied to two arguments
   but its type `Int -> Int' has only one

When visible type applications (e.g., `f @Int 1 2`, as in #13902) enter the
picture, we have a choice in deciding whether to count the type applications as
proper arguments:

   The function 'f' is applied to one visible type argument
     and two value arguments
   but its type `forall a. a -> a` has only one visible type argument
     and one value argument

Or whether to include the type applications as part of the herald itself:

   The expression 'f @Int' is applied to two arguments
   but its type `Int -> Int` has only one

The latter is easier to implement and is arguably easier to understand, so we
choose to implement that option.

Note [matchExpectedFunTys]
~~~~~~~~~~~~~~~~~~~~~~~~~~
matchExpectedFunTys checks that a sigma has the form
of an n-ary function.  It passes the decomposed type to the
thing_inside, and returns a wrapper to coerce between the two types

It's used wherever a language construct must have a functional type,
namely:
        A lambda expression
        A function definition
     An operator section

This function must be written CPS'd because it needs to fill in the
ExpTypes produced for arguments before it can fill in the ExpType
passed in.

-}

-- Use this one when you have an "expected" type.
-- This function skolemises at each polytype.
matchExpectedFunTys :: forall a.
                       SDoc   -- See Note [Herald for matchExpectedFunTys]
                    -> UserTypeCtxt
                    -> Arity
                    -> ExpRhoType      -- Skolemised
                    -> ([Scaled ExpSigmaType] -> ExpRhoType -> TcM a)
                    -> TcM (HsWrapper, a)
-- If    matchExpectedFunTys n ty = (_, wrap)
-- then  wrap : (t1 -> ... -> tn -> ty_r) ~> ty,
--   where [t1, ..., tn], ty_r are passed to the thing_inside
matchExpectedFunTys herald ctx arity orig_ty thing_inside
  = case orig_ty of
      Check ty -> go [] arity ty
      _        -> defer [] arity orig_ty
  where
    -- Skolemise any foralls /before/ the zero-arg case
    -- so that we guarantee to return a rho-type
    go acc_arg_tys n ty
      | (tvs, theta, _) <- tcSplitSigmaTy ty
      , not (null tvs && null theta)
      = do { (wrap_gen, (wrap_res, result)) <- tcSkolemise ctx ty $ \ty' ->
                                               go acc_arg_tys n ty'
           ; return (wrap_gen <.> wrap_res, result) }

    -- No more args; do this /before/ tcView, so
    -- that we do not unnecessarily unwrap synonyms
    go acc_arg_tys 0 rho_ty
      = do { result <- thing_inside (reverse acc_arg_tys) (mkCheckExpType rho_ty)
           ; return (idHsWrapper, result) }

    go acc_arg_tys n ty
      | Just ty' <- tcView ty = go acc_arg_tys n ty'

    go acc_arg_tys n (FunTy { ft_mult = mult, ft_af = af, ft_arg = arg_ty, ft_res = res_ty })
      = ASSERT( af == VisArg )
        do { (wrap_res, result) <- go ((Scaled mult $ mkCheckExpType arg_ty) : acc_arg_tys)
                                      (n-1) res_ty
           ; let fun_wrap = mkWpFun idHsWrapper wrap_res (Scaled mult arg_ty) res_ty doc
           ; return ( fun_wrap, result ) }
      where
        doc = text "When inferring the argument type of a function with type" <+>
              quotes (ppr orig_ty)

    go acc_arg_tys n ty@(TyVarTy tv)
      | isMetaTyVar tv
      = do { cts <- readMetaTyVar tv
           ; case cts of
               Indirect ty' -> go acc_arg_tys n ty'
               Flexi        -> defer acc_arg_tys n (mkCheckExpType ty) }

       -- In all other cases we bale out into ordinary unification
       -- However unlike the meta-tyvar case, we are sure that the
       -- number of arguments doesn't match arity of the original
       -- type, so we can add a bit more context to the error message
       -- (cf #7869).
       --
       -- It is not always an error, because specialized type may have
       -- different arity, for example:
       --
       -- > f1 = f2 'a'
       -- > f2 :: Monad m => m Bool
       -- > f2 = undefined
       --
       -- But in that case we add specialized type into error context
       -- anyway, because it may be useful. See also #9605.
    go acc_arg_tys n ty = addErrCtxtM (mk_ctxt acc_arg_tys ty) $
                          defer acc_arg_tys n (mkCheckExpType ty)

    ------------
    defer :: [Scaled ExpSigmaType] -> Arity -> ExpRhoType -> TcM (HsWrapper, a)
    defer acc_arg_tys n fun_ty
      = do { more_arg_tys <- replicateM n newInferExpType
           ; res_ty       <- newInferExpType
           ; result       <- thing_inside (reverse acc_arg_tys ++ (map unrestricted more_arg_tys)) res_ty
           ; more_arg_tys <- mapM readExpType more_arg_tys
           ; res_ty       <- readExpType res_ty
           ; let unif_fun_ty = mkVisFunTysMany more_arg_tys res_ty
           ; wrap <- tcSubType AppOrigin ctx unif_fun_ty fun_ty
                         -- Not a good origin at all :-(
           ; return (wrap, result) }

    ------------
    mk_ctxt :: [Scaled ExpSigmaType] -> TcType -> TidyEnv -> TcM (TidyEnv, MsgDoc)
    mk_ctxt arg_tys res_ty env
      = mkFunTysMsg env herald arg_tys' res_ty arity
      where
        arg_tys' = map (\(Scaled u v) -> Scaled u (checkingExpType "matchExpectedFunTys" v)) $
                   reverse arg_tys
            -- this is safe b/c we're called from "go"

mkFunTysMsg :: TidyEnv -> SDoc -> [Scaled TcType] -> TcType -> Arity
            -> TcM (TidyEnv, MsgDoc)
mkFunTysMsg env herald arg_tys res_ty n_val_args_in_call
  = do { (env', fun_rho) <- zonkTidyTcType env $
                            mkVisFunTys arg_tys res_ty

       ; let (all_arg_tys, _) = splitFunTys fun_rho
             n_fun_args = length all_arg_tys

             msg | n_val_args_in_call <= n_fun_args  -- Enough args, in the end
                 = text "In the result of a function call"
                 | otherwise
                 = hang (full_herald <> comma)
                      2 (sep [ text "but its type" <+> quotes (pprType fun_rho)
                             , if n_fun_args == 0 then text "has none"
                               else text "has only" <+> speakN n_fun_args])

       ; return (env', msg) }
 where
  full_herald = herald <+> speakNOf n_val_args_in_call (text "value argument")

----------------------
matchExpectedListTy :: TcRhoType -> TcM (TcCoercionN, TcRhoType)
-- Special case for lists
matchExpectedListTy exp_ty
 = do { (co, [elt_ty]) <- matchExpectedTyConApp listTyCon exp_ty
      ; return (co, elt_ty) }

---------------------
matchExpectedTyConApp :: TyCon                -- T :: forall kv1 ... kvm. k1 -> ... -> kn -> *
                      -> TcRhoType            -- orig_ty
                      -> TcM (TcCoercionN,    -- T k1 k2 k3 a b c ~N orig_ty
                              [TcSigmaType])  -- Element types, k1 k2 k3 a b c

-- It's used for wired-in tycons, so we call checkWiredInTyCon
-- Precondition: never called with FunTyCon
-- Precondition: input type :: *
-- Postcondition: (T k1 k2 k3 a b c) is well-kinded

matchExpectedTyConApp tc orig_ty
  = ASSERT(not $ isFunTyCon tc) go orig_ty
  where
    go ty
       | Just ty' <- tcView ty
       = go ty'

    go ty@(TyConApp tycon args)
       | tc == tycon  -- Common case
       = return (mkTcNomReflCo ty, args)

    go (TyVarTy tv)
       | isMetaTyVar tv
       = do { cts <- readMetaTyVar tv
            ; case cts of
                Indirect ty -> go ty
                Flexi       -> defer }

    go _ = defer

    -- If the common case does not occur, instantiate a template
    -- T k1 .. kn t1 .. tm, and unify with the original type
    -- Doing it this way ensures that the types we return are
    -- kind-compatible with T.  For example, suppose we have
    --       matchExpectedTyConApp T (f Maybe)
    -- where data T a = MkT a
    -- Then we don't want to instantiate T's data constructors with
    --    (a::*) ~ Maybe
    -- because that'll make types that are utterly ill-kinded.
    -- This happened in #7368
    defer
      = do { (_, arg_tvs) <- newMetaTyVars (tyConTyVars tc)
           ; traceTc "matchExpectedTyConApp" (ppr tc $$ ppr (tyConTyVars tc) $$ ppr arg_tvs)
           ; let args = mkTyVarTys arg_tvs
                 tc_template = mkTyConApp tc args
           ; co <- unifyType Nothing tc_template orig_ty
           ; return (co, args) }

----------------------
matchExpectedAppTy :: TcRhoType                         -- orig_ty
                   -> TcM (TcCoercion,                   -- m a ~N orig_ty
                           (TcSigmaType, TcSigmaType))  -- Returns m, a
-- If the incoming type is a mutable type variable of kind k, then
-- matchExpectedAppTy returns a new type variable (m: * -> k); note the *.

matchExpectedAppTy orig_ty
  = go orig_ty
  where
    go ty
      | Just ty' <- tcView ty = go ty'

      | Just (fun_ty, arg_ty) <- tcSplitAppTy_maybe ty
      = return (mkTcNomReflCo orig_ty, (fun_ty, arg_ty))

    go (TyVarTy tv)
      | isMetaTyVar tv
      = do { cts <- readMetaTyVar tv
           ; case cts of
               Indirect ty -> go ty
               Flexi       -> defer }

    go _ = defer

    -- Defer splitting by generating an equality constraint
    defer
      = do { ty1 <- newFlexiTyVarTy kind1
           ; ty2 <- newFlexiTyVarTy kind2
           ; co <- unifyType Nothing (mkAppTy ty1 ty2) orig_ty
           ; return (co, (ty1, ty2)) }

    orig_kind = tcTypeKind orig_ty
    kind1 = mkVisFunTyMany liftedTypeKind orig_kind
    kind2 = liftedTypeKind    -- m :: * -> k
                              -- arg type :: *

{-
************************************************************************
*                                                                      *
                Subsumption checking
*                                                                      *
************************************************************************

Note [Subsumption checking: tcSubType]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
All the tcSubType calls have the form
                tcSubType actual_ty expected_ty
which checks
                actual_ty <= expected_ty

That is, that a value of type actual_ty is acceptable in
a place expecting a value of type expected_ty.  I.e. that

    actual ty   is more polymorphic than   expected_ty

It returns a wrapper function
        co_fn :: actual_ty ~ expected_ty
which takes an HsExpr of type actual_ty into one of type
expected_ty.
-}


-----------------
-- tcWrapResult needs both un-type-checked (for origins and error messages)
-- and type-checked (for wrapping) expressions
tcWrapResult :: HsExpr GhcRn -> HsExpr GhcTc -> TcSigmaType -> ExpRhoType
             -> TcM (HsExpr GhcTc)
tcWrapResult rn_expr = tcWrapResultO (exprCtOrigin rn_expr) rn_expr

tcWrapResultO :: CtOrigin -> HsExpr GhcRn -> HsExpr GhcTc -> TcSigmaType -> ExpRhoType
               -> TcM (HsExpr GhcTc)
tcWrapResultO orig rn_expr expr actual_ty res_ty
  = do { traceTc "tcWrapResult" (vcat [ text "Actual:  " <+> ppr actual_ty
                                      , text "Expected:" <+> ppr res_ty ])
       ; wrap <- tcSubTypeNC orig GenSigCtxt (Just (ppr rn_expr)) actual_ty res_ty
       ; return (mkHsWrap wrap expr) }

tcWrapResultMono :: HsExpr GhcRn -> HsExpr GhcTc
                 -> TcRhoType   -- Actual -- a rho-type not a sigma-type
                 -> ExpRhoType  -- Expected
                 -> TcM (HsExpr GhcTc)
-- A version of tcWrapResult to use when the actual type is a
-- rho-type, so nothing to instantiate; just go straight to unify.
-- It means we don't need to pass in a CtOrigin
tcWrapResultMono rn_expr expr act_ty res_ty
  = ASSERT2( isRhoTy act_ty, ppr act_ty $$ ppr rn_expr )
    do { co <- case res_ty of
                  Infer inf_res -> fillInferResult act_ty inf_res
                  Check exp_ty  -> unifyType (Just (ppr rn_expr)) act_ty exp_ty
       ; return (mkHsWrapCo co expr) }

------------------------
tcSubTypePat :: CtOrigin -> UserTypeCtxt
            -> ExpSigmaType -> TcSigmaType -> TcM HsWrapper
-- Used in patterns; polarity is backwards compared
--   to tcSubType
-- If wrap = tc_sub_type_et t1 t2
--    => wrap :: t1 ~> t2
tcSubTypePat inst_orig ctxt (Check ty_actual) ty_expected
  = tc_sub_type unifyTypeET inst_orig ctxt ty_actual ty_expected

tcSubTypePat _ _ (Infer inf_res) ty_expected
  = do { co <- fillInferResult ty_expected inf_res
               -- In patterns we do not instantatiate

       ; return (mkWpCastN (mkTcSymCo co)) }

---------------
tcSubType :: CtOrigin -> UserTypeCtxt
          -> TcSigmaType  -- Actual
          -> ExpRhoType   -- Expected
          -> TcM HsWrapper
-- Checks that 'actual' is more polymorphic than 'expected'
tcSubType orig ctxt ty_actual ty_expected
  = addSubTypeCtxt ty_actual ty_expected $
    do { traceTc "tcSubType" (vcat [pprUserTypeCtxt ctxt, ppr ty_actual, ppr ty_expected])
       ; tcSubTypeNC orig ctxt Nothing ty_actual ty_expected }

tcSubTypeNC :: CtOrigin       -- Used when instantiating
            -> UserTypeCtxt   -- Used when skolemising
            -> Maybe SDoc     -- The expression that has type 'actual' (if known)
            -> TcSigmaType            -- Actual type
            -> ExpRhoType             -- Expected type
            -> TcM HsWrapper
tcSubTypeNC inst_orig ctxt m_thing ty_actual res_ty
  = case res_ty of
      Check ty_expected -> tc_sub_type (unifyType m_thing) inst_orig ctxt
                                       ty_actual ty_expected

      Infer inf_res -> do { (wrap, rho) <- topInstantiate inst_orig ty_actual
                                   -- See Note [Instantiation of InferResult]
                          ; co <- fillInferResult rho inf_res
                          ; return (mkWpCastN co <.> wrap) }

{- Note [Instantiation of InferResult]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We now always instantiate before filling in InferResult, so that
the result is a TcRhoType: see #17173 for discussion.

For example:

1. Consider
    f x = (*)
   We want to instantiate the type of (*) before returning, else we
   will infer the type
     f :: forall {a}. a -> forall b. Num b => b -> b -> b
   This is surely confusing for users.

   And worse, the monomorphism restriction won't work properly. The MR is
   dealt with in simplifyInfer, and simplifyInfer has no way of
   instantiating. This could perhaps be worked around, but it may be
   hard to know even when instantiation should happen.

2. Another reason.  Consider
       f :: (?x :: Int) => a -> a
       g y = let ?x = 3::Int in f
   Here want to instantiate f's type so that the ?x::Int constraint
   gets discharged by the enclosing implicit-parameter binding.

3. Suppose one defines plus = (+). If we instantiate lazily, we will
   infer plus :: forall a. Num a => a -> a -> a. However, the monomorphism
   restriction compels us to infer
      plus :: Integer -> Integer -> Integer
   (or similar monotype). Indeed, the only way to know whether to apply
   the monomorphism restriction at all is to instantiate

There is one place where we don't want to instantiate eagerly,
namely in GHC.Tc.Module.tcRnExpr, which implements GHCi's :type
command. See Note [Implementing :type] in GHC.Tc.Module.
-}

---------------
tcSubTypeSigma :: UserTypeCtxt -> TcSigmaType -> TcSigmaType -> TcM HsWrapper
-- External entry point, but no ExpTypes on either side
-- Checks that actual <= expected
-- Returns HsWrapper :: actual ~ expected
tcSubTypeSigma ctxt ty_actual ty_expected
  = tc_sub_type (unifyType Nothing) eq_orig ctxt ty_actual ty_expected
  where
    eq_orig = TypeEqOrigin { uo_actual   = ty_actual
                           , uo_expected = ty_expected
                           , uo_thing    = Nothing
                           , uo_visible  = True }

---------------
tc_sub_type :: (TcType -> TcType -> TcM TcCoercionN)  -- How to unify
            -> CtOrigin       -- Used when instantiating
            -> UserTypeCtxt   -- Used when skolemising
            -> TcSigmaType    -- Actual; a sigma-type
            -> TcSigmaType    -- Expected; also a sigma-type
            -> TcM HsWrapper
-- Checks that actual_ty is more polymorphic than expected_ty
-- If wrap = tc_sub_type t1 t2
--    => wrap :: t1 ~> t2
tc_sub_type unify inst_orig ctxt ty_actual ty_expected
  | definitely_poly ty_expected      -- See Note [Don't skolemise unnecessarily]
  , not (possibly_poly ty_actual)
  = do { traceTc "tc_sub_type (drop to equality)" $
         vcat [ text "ty_actual   =" <+> ppr ty_actual
              , text "ty_expected =" <+> ppr ty_expected ]
       ; mkWpCastN <$>
         unify ty_actual ty_expected }

  | otherwise   -- This is the general case
  = do { traceTc "tc_sub_type (general case)" $
         vcat [ text "ty_actual   =" <+> ppr ty_actual
              , text "ty_expected =" <+> ppr ty_expected ]

       ; (sk_wrap, inner_wrap)
           <- tcSkolemise ctxt ty_expected $ \ sk_rho ->
              do { (wrap, rho_a) <- topInstantiate inst_orig ty_actual
                 ; cow           <- unify rho_a sk_rho
                 ; return (mkWpCastN cow <.> wrap) }

       ; return (sk_wrap <.> inner_wrap) }
  where
    possibly_poly ty = not (isRhoTy ty)

    definitely_poly ty
      | (tvs, theta, tau) <- tcSplitSigmaTy ty
      , (tv:_) <- tvs
      , null theta
      , isInsolubleOccursCheck NomEq tv tau
      = True
      | otherwise
      = False

------------------------
addSubTypeCtxt :: TcType -> ExpType -> TcM a -> TcM a
addSubTypeCtxt ty_actual ty_expected thing_inside
 | isRhoTy ty_actual        -- If there is no polymorphism involved, the
 , isRhoExpTy ty_expected   -- TypeEqOrigin stuff (added by the _NC functions)
 = thing_inside             -- gives enough context by itself
 | otherwise
 = addErrCtxtM mk_msg thing_inside
  where
    mk_msg tidy_env
      = do { (tidy_env, ty_actual)   <- zonkTidyTcType tidy_env ty_actual
                   -- might not be filled if we're debugging. ugh.
           ; mb_ty_expected          <- readExpType_maybe ty_expected
           ; (tidy_env, ty_expected) <- case mb_ty_expected of
                                          Just ty -> second mkCheckExpType <$>
                                                     zonkTidyTcType tidy_env ty
                                          Nothing -> return (tidy_env, ty_expected)
           ; ty_expected             <- readExpType ty_expected
           ; (tidy_env, ty_expected) <- zonkTidyTcType tidy_env ty_expected
           ; let msg = vcat [ hang (text "When checking that:")
                                 4 (ppr ty_actual)
                            , nest 2 (hang (text "is more polymorphic than:")
                                         2 (ppr ty_expected)) ]
           ; return (tidy_env, msg) }

{- Note [Don't skolemise unnecessarily]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we are trying to solve
    (Char->Char) <= (forall a. a->a)
We could skolemise the 'forall a', and then complain
that (Char ~ a) is insoluble; but that's a pretty obscure
error.  It's better to say that
    (Char->Char) ~ (forall a. a->a)
fails.

So roughly:
 * if the ty_expected has an outermost forall
      (i.e. skolemisation is the next thing we'd do)
 * and the ty_actual has no top-level polymorphism (but looking deeply)
then we can revert to simple equality.  But we need to be careful.
These examples are all fine:

 * (Char->Char) <= (forall a. Char -> Char)
      ty_expected isn't really polymorphic

 * (Char->Char) <= (forall a. (a~Char) => a -> a)
      ty_expected isn't really polymorphic

 * (Char->Char) <= (forall a. F [a] Char -> Char)
                   where type instance F [x] t = t
     ty_expected isn't really polymorphic

If we prematurely go to equality we'll reject a program we should
accept (e.g. #13752).  So the test (which is only to improve
error message) is very conservative:
 * ty_actual is /definitely/ monomorphic
 * ty_expected is /definitely/ polymorphic

Note [Settting the argument context]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider we are doing the ambiguity check for the (bogus)
  f :: (forall a b. C b => a -> a) -> Int

We'll call
   tcSubType ((forall a b. C b => a->a) -> Int )
             ((forall a b. C b => a->a) -> Int )

with a UserTypeCtxt of (FunSigCtxt "f").  Then we'll do the co/contra thing
on the argument type of the (->) -- and at that point we want to switch
to a UserTypeCtxt of GenSigCtxt.  Why?

* Error messages.  If we stick with FunSigCtxt we get errors like
     * Could not deduce: C b
       from the context: C b0
        bound by the type signature for:
            f :: forall a b. C b => a->a
  But of course f does not have that type signature!
  Example tests: T10508, T7220a, Simple14

* Implications. We may decide to build an implication for the whole
  ambiguity check, but we don't need one for each level within it,
  and GHC.Tc.Utils.Unify.alwaysBuildImplication checks the UserTypeCtxt.
  See Note [When to build an implication]

Note [Wrapper returned from tcSubMult]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
There is no notion of multiplicity coercion in Core, therefore the wrapper
returned by tcSubMult (and derived functions such as tcCheckUsage and
checkManyPattern) is quite unlike any other wrapper: it checks whether the
coercion produced by the constraint solver is trivial, producing a type error
is it is not. This is implemented via the WpMultCoercion wrapper, as desugared
by GHC.HsToCore.Binds.dsHsWrapper, which does the reflexivity check.

This wrapper needs to be placed in the term; otherwise, checking of the
eventual coercion won't be triggered during desugaring. But it can be put
anywhere, since it doesn't affect the desugared code.

Why do we check this in the desugarer? It's a convenient place, since it's
right after all the constraints are solved. We need the constraints to be
solved to check whether they are trivial or not. Plus there is precedent for
type errors during desuraging (such as the levity polymorphism
restriction). An alternative would be to have a kind of constraint which can
only produce trivial evidence, then this check would happen in the constraint
solver.
-}

tcSubMult :: CtOrigin -> Mult -> Mult -> TcM HsWrapper
tcSubMult origin w_actual w_expected
  | Just (w1, w2) <- isMultMul w_actual =
  do { w1 <- tcSubMult origin w1 w_expected
     ; w2 <- tcSubMult origin w2 w_expected
     ; return (w1 <.> w2) }
  -- Currently, we consider p*q and sup p q to be equal.  Therefore, p*q <= r is
  -- equivalent to p <= r and q <= r.  For other cases, we approximate p <= q by p
  -- ~ q.  This is not complete, but it's sound. See also Note [Overapproximating
  -- multiplicities] in Multiplicity.
tcSubMult origin w_actual w_expected =
  case submult w_actual w_expected of
    Submult -> return WpHole
    Unknown -> tcEqMult origin w_actual w_expected

tcEqMult :: CtOrigin -> Mult -> Mult -> TcM HsWrapper
tcEqMult origin w_actual w_expected = do
  {
  -- Note that here we do not call to `submult`, so we check
  -- for strict equality.
  ; coercion <- uType TypeLevel origin w_actual w_expected
  ; return $ if isReflCo coercion then WpHole else WpMultCoercion coercion }


{- *********************************************************************
*                                                                      *
                    Generalisation
*                                                                      *
********************************************************************* -}

{- Note [Skolemisation]
~~~~~~~~~~~~~~~~~~~~~~~
tcSkolemise takes "expected type" and strip off quantifiers to expose the
type underneath, binding the new skolems for the 'thing_inside'
The returned 'HsWrapper' has type (specific_ty -> expected_ty).

Note that for a nested type like
   forall a. Eq a => forall b. Ord b => blah
we still only build one implication constraint
   forall a b. (Eq a, Ord b) => <constraints>
This is just an optimisation, but it's why we use topSkolemise to
build the pieces from all the layers, before making a single call
to checkConstraints.

tcSkolemiseScoped is very similar, but differs in two ways:

* It deals specially with just the outer forall, bringing those
  type variables into lexical scope.  To my surprise, I found that
  doing this regardless (in tcSkolemise) caused a non-trivial (1%-ish)
  perf hit on the compiler.

* It always calls checkConstraints, even if there are no skolem
  variables at all.  Reason: there might be nested deferred errors
  that must not be allowed to float to top level.
  See Note [When to build an implication] below.
-}

tcSkolemise, tcSkolemiseScoped, tcSkolemiseAlways
    :: UserTypeCtxt -> TcSigmaType
    -> (TcType -> TcM result)
    -> TcM (HsWrapper, result)
        -- ^ The wrapper has type: spec_ty ~> expected_ty

tcSkolemiseScoped ctxt expected_ty thing_inside
  = do { (wrap, tv_prs, given, rho_ty) <- topSkolemise expected_ty
       ; let skol_tvs  = map snd tv_prs
             skol_info = SigSkol ctxt expected_ty tv_prs

       ; (ev_binds, res)
             <- checkConstraints skol_info skol_tvs given $
                tcExtendNameTyVarEnv tv_prs               $
                thing_inside rho_ty

       ; return (wrap <.> mkWpLet ev_binds, res) }

tcSkolemise ctxt expected_ty thing_inside
  | isRhoTy expected_ty  -- Short cut for common case
  = do { res <- thing_inside expected_ty
       ; return (idHsWrapper, res) }
  | otherwise
  = tcSkolemiseAlways ctxt expected_ty thing_inside

tcSkolemiseAlways ctxt expected_ty thing_inside
  = do  { (wrap, tv_prs, given, rho_ty) <- topSkolemise expected_ty

        ; let skol_tvs  = map snd tv_prs
              skol_info = SigSkol ctxt expected_ty tv_prs

        ; (ev_binds, result)
              <- checkConstraints skol_info skol_tvs given $
                 thing_inside rho_ty

        ; return (wrap <.> mkWpLet ev_binds, result) }
          -- The ev_binds returned by checkConstraints is very
          -- often empty, in which case mkWpLet is a no-op

-- | Variant of 'tcSkolemise' that takes an ExpType
tcSkolemiseET :: UserTypeCtxt -> ExpSigmaType
              -> (ExpRhoType -> TcM result)
              -> TcM (HsWrapper, result)
tcSkolemiseET _ et@(Infer {}) thing_inside
  = (idHsWrapper, ) <$> thing_inside et
tcSkolemiseET ctxt (Check ty) thing_inside
  = tcSkolemise ctxt ty $ \rho_ty ->
    thing_inside (mkCheckExpType rho_ty)

checkConstraints :: SkolemInfo
                 -> [TcTyVar]           -- Skolems
                 -> [EvVar]             -- Given
                 -> TcM result
                 -> TcM (TcEvBinds, result)

checkConstraints skol_info skol_tvs given thing_inside
  = do { implication_needed <- implicationNeeded skol_info skol_tvs given

       ; if implication_needed
         then do { (tclvl, wanted, result) <- pushLevelAndCaptureConstraints thing_inside
                 ; (implics, ev_binds) <- buildImplicationFor tclvl skol_info skol_tvs given wanted
                 ; traceTc "checkConstraints" (ppr tclvl $$ ppr skol_tvs)
                 ; emitImplications implics
                 ; return (ev_binds, result) }

         else -- Fast path.  We check every function argument with tcCheckPolyExpr,
              -- which uses tcSkolemise and hence checkConstraints.
              -- So this fast path is well-exercised
              do { res <- thing_inside
                 ; return (emptyTcEvBinds, res) } }

checkTvConstraints :: SkolemInfo
                   -> [TcTyVar]          -- Skolem tyvars
                   -> TcM result
                   -> TcM result

checkTvConstraints skol_info skol_tvs thing_inside
  = do { (tclvl, wanted, result) <- pushLevelAndCaptureConstraints thing_inside
       ; emitResidualTvConstraint skol_info skol_tvs tclvl wanted
       ; return result }

emitResidualTvConstraint :: SkolemInfo -> [TcTyVar]
                         -> TcLevel -> WantedConstraints -> TcM ()
emitResidualTvConstraint skol_info skol_tvs tclvl wanted
  | isEmptyWC wanted
  = return ()

  | otherwise
  = do { implic <- buildTvImplication skol_info skol_tvs tclvl wanted
       ; emitImplication implic }

buildTvImplication :: SkolemInfo -> [TcTyVar]
                   -> TcLevel -> WantedConstraints -> TcM Implication
buildTvImplication skol_info skol_tvs tclvl wanted
  = do { ev_binds <- newNoTcEvBinds  -- Used for equalities only, so all the constraints
                                     -- are solved by filling in coercion holes, not
                                     -- by creating a value-level evidence binding
       ; implic   <- newImplication

       ; return (implic { ic_tclvl     = tclvl
                        , ic_skols     = skol_tvs
                        , ic_no_eqs    = True
                        , ic_wanted    = wanted
                        , ic_binds     = ev_binds
                        , ic_info      = skol_info }) }

implicationNeeded :: SkolemInfo -> [TcTyVar] -> [EvVar] -> TcM Bool
-- See Note [When to build an implication]
implicationNeeded skol_info skol_tvs given
  | null skol_tvs
  , null given
  , not (alwaysBuildImplication skol_info)
  = -- Empty skolems and givens
    do { tc_lvl <- getTcLevel
       ; if not (isTopTcLevel tc_lvl)  -- No implication needed if we are
         then return False             -- already inside an implication
         else
    do { dflags <- getDynFlags       -- If any deferral can happen,
                                     -- we must build an implication
       ; return (gopt Opt_DeferTypeErrors dflags ||
                 gopt Opt_DeferTypedHoles dflags ||
                 gopt Opt_DeferOutOfScopeVariables dflags) } }

  | otherwise     -- Non-empty skolems or givens
  = return True   -- Definitely need an implication

alwaysBuildImplication :: SkolemInfo -> Bool
-- See Note [When to build an implication]
alwaysBuildImplication _ = False

{-  Commmented out for now while I figure out about error messages.
    See #14185

alwaysBuildImplication (SigSkol ctxt _ _)
  = case ctxt of
      FunSigCtxt {} -> True  -- RHS of a binding with a signature
      _             -> False
alwaysBuildImplication (RuleSkol {})      = True
alwaysBuildImplication (InstSkol {})      = True
alwaysBuildImplication (FamInstSkol {})   = True
alwaysBuildImplication _                  = False
-}

buildImplicationFor :: TcLevel -> SkolemInfo -> [TcTyVar]
                   -> [EvVar] -> WantedConstraints
                   -> TcM (Bag Implication, TcEvBinds)
buildImplicationFor tclvl skol_info skol_tvs given wanted
  | isEmptyWC wanted && null given
             -- Optimisation : if there are no wanteds, and no givens
             -- don't generate an implication at all.
             -- Reason for the (null given): we don't want to lose
             -- the "inaccessible alternative" error check
  = return (emptyBag, emptyTcEvBinds)

  | otherwise
  = ASSERT2( all (isSkolemTyVar <||> isTyVarTyVar) skol_tvs, ppr skol_tvs )
      -- Why allow TyVarTvs? Because implicitly declared kind variables in
      -- non-CUSK type declarations are TyVarTvs, and we need to bring them
      -- into scope as a skolem in an implication. This is OK, though,
      -- because TyVarTvs will always remain tyvars, even after unification.
    do { ev_binds_var <- newTcEvBinds
       ; implic <- newImplication
       ; let implic' = implic { ic_tclvl  = tclvl
                              , ic_skols  = skol_tvs
                              , ic_given  = given
                              , ic_wanted = wanted
                              , ic_binds  = ev_binds_var
                              , ic_info   = skol_info }

       ; return (unitBag implic', TcEvBinds ev_binds_var) }

{- Note [When to build an implication]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have some 'skolems' and some 'givens', and we are
considering whether to wrap the constraints in their scope into an
implication.  We must /always/ so if either 'skolems' or 'givens' are
non-empty.  But what if both are empty?  You might think we could
always drop the implication.  Other things being equal, the fewer
implications the better.  Less clutter and overhead.  But we must
take care:

* If we have an unsolved [W] g :: a ~# b, and -fdefer-type-errors,
  we'll make a /term-level/ evidence binding for 'g = error "blah"'.
  We must have an EvBindsVar those bindings!, otherwise they end up as
  top-level unlifted bindings, which are verboten. This only matters
  at top level, so we check for that
  See also Note [Deferred errors for coercion holes] in GHC.Tc.Errors.
  cf #14149 for an example of what goes wrong.

* If you have
     f :: Int;  f = f_blah
     g :: Bool; g = g_blah
  If we don't build an implication for f or g (no tyvars, no givens),
  the constraints for f_blah and g_blah are solved together.  And that
  can yield /very/ confusing error messages, because we can get
      [W] C Int b1    -- from f_blah
      [W] C Int b2    -- from g_blan
  and fundpes can yield [D] b1 ~ b2, even though the two functions have
  literally nothing to do with each other.  #14185 is an example.
  Building an implication keeps them separate.
-}

{-
************************************************************************
*                                                                      *
                Boxy unification
*                                                                      *
************************************************************************

The exported functions are all defined as versions of some
non-exported generic functions.
-}

unifyType :: Maybe SDoc  -- ^ If present, the thing that has type ty1
          -> TcTauType -> TcTauType    -- ty1, ty2
          -> TcM TcCoercionN           -- :: ty1 ~# ty2
-- Actual and expected types
-- Returns a coercion : ty1 ~ ty2
unifyType thing ty1 ty2
  = uType TypeLevel origin ty1 ty2
  where
    origin = TypeEqOrigin { uo_actual   = ty1
                          , uo_expected = ty2
                          , uo_thing    = ppr <$> thing
                          , uo_visible  = True }

unifyTypeET :: TcTauType -> TcTauType -> TcM CoercionN
-- Like unifyType, but swap expected and actual in error messages
-- This is used when typechecking patterns
unifyTypeET ty1 ty2
  = uType TypeLevel origin ty1 ty2
  where
    origin = TypeEqOrigin { uo_actual   = ty2   -- NB swapped
                          , uo_expected = ty1   -- NB swapped
                          , uo_thing    = Nothing
                          , uo_visible  = True }


unifyKind :: Maybe SDoc -> TcKind -> TcKind -> TcM CoercionN
unifyKind mb_thing ty1 ty2
  = uType KindLevel origin ty1 ty2
  where
    origin = TypeEqOrigin { uo_actual   = ty1
                          , uo_expected = ty2
                          , uo_thing    = mb_thing
                          , uo_visible  = True }


{-
%************************************************************************
%*                                                                      *
                 uType and friends
%*                                                                      *
%************************************************************************

uType is the heart of the unifier.
-}

uType, uType_defer
  :: TypeOrKind
  -> CtOrigin
  -> TcType    -- ty1 is the *actual* type
  -> TcType    -- ty2 is the *expected* type
  -> TcM CoercionN

--------------
-- It is always safe to defer unification to the main constraint solver
-- See Note [Deferred unification]
uType_defer t_or_k origin ty1 ty2
  = do { co <- emitWantedEq origin t_or_k Nominal ty1 ty2

       -- Error trace only
       -- NB. do *not* call mkErrInfo unless tracing is on,
       --     because it is hugely expensive (#5631)
       ; whenDOptM Opt_D_dump_tc_trace $ do
            { ctxt <- getErrCtxt
            ; doc <- mkErrInfo emptyTidyEnv ctxt
            ; traceTc "utype_defer" (vcat [ debugPprType ty1
                                          , debugPprType ty2
                                          , pprCtOrigin origin
                                          , doc])
            ; traceTc "utype_defer2" (ppr co)
            }
       ; return co }

--------------
uType t_or_k origin orig_ty1 orig_ty2
  = do { tclvl <- getTcLevel
       ; traceTc "u_tys" $ vcat
              [ text "tclvl" <+> ppr tclvl
              , sep [ ppr orig_ty1, text "~", ppr orig_ty2]
              , pprCtOrigin origin]
       ; co <- go orig_ty1 orig_ty2
       ; if isReflCo co
            then traceTc "u_tys yields no coercion" Outputable.empty
            else traceTc "u_tys yields coercion:" (ppr co)
       ; return co }
  where
    go :: TcType -> TcType -> TcM CoercionN
        -- The arguments to 'go' are always semantically identical
        -- to orig_ty{1,2} except for looking through type synonyms

     -- Unwrap casts before looking for variables. This way, we can easily
     -- recognize (t |> co) ~ (t |> co), which is nice. Previously, we
     -- didn't do it this way, and then the unification above was deferred.
    go (CastTy t1 co1) t2
      = do { co_tys <- uType t_or_k origin t1 t2
           ; return (mkCoherenceLeftCo Nominal t1 co1 co_tys) }

    go t1 (CastTy t2 co2)
      = do { co_tys <- uType t_or_k origin t1 t2
           ; return (mkCoherenceRightCo Nominal t2 co2 co_tys) }

        -- Variables; go for uUnfilledVar
        -- Note that we pass in *original* (before synonym expansion),
        -- so that type variables tend to get filled in with
        -- the most informative version of the type
    go (TyVarTy tv1) ty2
      = do { lookup_res <- lookupTcTyVar tv1
           ; case lookup_res of
               Filled ty1   -> do { traceTc "found filled tyvar" (ppr tv1 <+> text ":->" <+> ppr ty1)
                                  ; go ty1 ty2 }
               Unfilled _ -> uUnfilledVar origin t_or_k NotSwapped tv1 ty2 }
    go ty1 (TyVarTy tv2)
      = do { lookup_res <- lookupTcTyVar tv2
           ; case lookup_res of
               Filled ty2   -> do { traceTc "found filled tyvar" (ppr tv2 <+> text ":->" <+> ppr ty2)
                                  ; go ty1 ty2 }
               Unfilled _ -> uUnfilledVar origin t_or_k IsSwapped tv2 ty1 }

      -- See Note [Expanding synonyms during unification]
    go ty1@(TyConApp tc1 []) (TyConApp tc2 [])
      | tc1 == tc2
      = return $ mkNomReflCo ty1

        -- See Note [Expanding synonyms during unification]
        --
        -- Also NB that we recurse to 'go' so that we don't push a
        -- new item on the origin stack. As a result if we have
        --   type Foo = Int
        -- and we try to unify  Foo ~ Bool
        -- we'll end up saying "can't match Foo with Bool"
        -- rather than "can't match "Int with Bool".  See #4535.
    go ty1 ty2
      | Just ty1' <- tcView ty1 = go ty1' ty2
      | Just ty2' <- tcView ty2 = go ty1  ty2'

    -- Functions (t1 -> t2) just check the two parts
    -- Do not attempt (c => t); just defer
    go (FunTy { ft_af = VisArg, ft_mult = w1, ft_arg = arg1, ft_res = res1 })
       (FunTy { ft_af = VisArg, ft_mult = w2, ft_arg = arg2, ft_res = res2 })
      = do { co_l <- uType t_or_k origin arg1 arg2
           ; co_r <- uType t_or_k origin res1 res2
           ; co_w <- uType t_or_k origin w1 w2
           ; return $ mkFunCo Nominal co_w co_l co_r }

        -- Always defer if a type synonym family (type function)
        -- is involved.  (Data families behave rigidly.)
    go ty1@(TyConApp tc1 _) ty2
      | isTypeFamilyTyCon tc1 = defer ty1 ty2
    go ty1 ty2@(TyConApp tc2 _)
      | isTypeFamilyTyCon tc2 = defer ty1 ty2

    go (TyConApp tc1 tys1) (TyConApp tc2 tys2)
      -- See Note [Mismatched type lists and application decomposition]
      | tc1 == tc2, equalLength tys1 tys2
      = ASSERT2( isGenerativeTyCon tc1 Nominal, ppr tc1 )
        do { cos <- zipWith3M (uType t_or_k) origins' tys1 tys2
           ; return $ mkTyConAppCo Nominal tc1 cos }
      where
        origins' = map (\is_vis -> if is_vis then origin else toInvisibleOrigin origin)
                       (tcTyConVisibilities tc1)

    go (LitTy m) ty@(LitTy n)
      | m == n
      = return $ mkNomReflCo ty

        -- See Note [Care with type applications]
        -- Do not decompose FunTy against App;
        -- it's often a type error, so leave it for the constraint solver
    go (AppTy s1 t1) (AppTy s2 t2)
      = go_app (isNextArgVisible s1) s1 t1 s2 t2

    go (AppTy s1 t1) (TyConApp tc2 ts2)
      | Just (ts2', t2') <- snocView ts2
      = ASSERT( not (mustBeSaturated tc2) )
        go_app (isNextTyConArgVisible tc2 ts2') s1 t1 (TyConApp tc2 ts2') t2'

    go (TyConApp tc1 ts1) (AppTy s2 t2)
      | Just (ts1', t1') <- snocView ts1
      = ASSERT( not (mustBeSaturated tc1) )
        go_app (isNextTyConArgVisible tc1 ts1') (TyConApp tc1 ts1') t1' s2 t2

    go (CoercionTy co1) (CoercionTy co2)
      = do { let ty1 = coercionType co1
                 ty2 = coercionType co2
           ; kco <- uType KindLevel
                          (KindEqOrigin orig_ty1 (Just orig_ty2) origin
                                        (Just t_or_k))
                          ty1 ty2
           ; return $ mkProofIrrelCo Nominal kco co1 co2 }

        -- Anything else fails
        -- E.g. unifying for-all types, which is relative unusual
    go ty1 ty2 = defer ty1 ty2

    ------------------
    defer ty1 ty2   -- See Note [Check for equality before deferring]
      | ty1 `tcEqType` ty2 = return (mkNomReflCo ty1)
      | otherwise          = uType_defer t_or_k origin ty1 ty2

    ------------------
    go_app vis s1 t1 s2 t2
      = do { co_s <- uType t_or_k origin s1 s2
           ; let arg_origin
                   | vis       = origin
                   | otherwise = toInvisibleOrigin origin
           ; co_t <- uType t_or_k arg_origin t1 t2
           ; return $ mkAppCo co_s co_t }

{- Note [Check for equality before deferring]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Particularly in ambiguity checks we can get equalities like (ty ~ ty).
If ty involves a type function we may defer, which isn't very sensible.
An egregious example of this was in test T9872a, which has a type signature
       Proxy :: Proxy (Solutions Cubes)
Doing the ambiguity check on this signature generates the equality
   Solutions Cubes ~ Solutions Cubes
and currently the constraint solver normalises both sides at vast cost.
This little short-cut in 'defer' helps quite a bit.

Note [Care with type applications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Note: type applications need a bit of care!
They can match FunTy and TyConApp, so use splitAppTy_maybe
NB: we've already dealt with type variables and Notes,
so if one type is an App the other one jolly well better be too

Note [Mismatched type lists and application decomposition]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When we find two TyConApps, you might think that the argument lists
are guaranteed equal length.  But they aren't. Consider matching
        w (T x) ~ Foo (T x y)
We do match (w ~ Foo) first, but in some circumstances we simply create
a deferred constraint; and then go ahead and match (T x ~ T x y).
This came up in #3950.

So either
   (a) either we must check for identical argument kinds
       when decomposing applications,

   (b) or we must be prepared for ill-kinded unification sub-problems

Currently we adopt (b) since it seems more robust -- no need to maintain
a global invariant.

Note [Expanding synonyms during unification]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We expand synonyms during unification, but:
 * We expand *after* the variable case so that we tend to unify
   variables with un-expanded type synonym. This just makes it
   more likely that the inferred types will mention type synonyms
   understandable to the user

 * Similarly, we expand *after* the CastTy case, just in case the
   CastTy wraps a variable.

 * We expand *before* the TyConApp case.  For example, if we have
      type Phantom a = Int
   and are unifying
      Phantom Int ~ Phantom Char
   it is *wrong* to unify Int and Char.

 * The problem case immediately above can happen only with arguments
   to the tycon. So we check for nullary tycons *before* expanding.
   This is particularly helpful when checking (* ~ *), because * is
   now a type synonym.

Note [Deferred Unification]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
We may encounter a unification ty1 ~ ty2 that cannot be performed syntactically,
and yet its consistency is undetermined. Previously, there was no way to still
make it consistent. So a mismatch error was issued.

Now these unifications are deferred until constraint simplification, where type
family instances and given equations may (or may not) establish the consistency.
Deferred unifications are of the form
                F ... ~ ...
or              x ~ ...
where F is a type function and x is a type variable.
E.g.
        id :: x ~ y => x -> y
        id e = e

involves the unification x = y. It is deferred until we bring into account the
context x ~ y to establish that it holds.

If available, we defer original types (rather than those where closed type
synonyms have already been expanded via tcCoreView).  This is, as usual, to
improve error messages.


************************************************************************
*                                                                      *
                 uUnfilledVar and friends
*                                                                      *
************************************************************************

@uunfilledVar@ is called when at least one of the types being unified is a
variable.  It does {\em not} assume that the variable is a fixed point
of the substitution; rather, notice that @uVar@ (defined below) nips
back into @uTys@ if it turns out that the variable is already bound.
-}

----------
uUnfilledVar :: CtOrigin
             -> TypeOrKind
             -> SwapFlag
             -> TcTyVar        -- Tyvar 1: not necessarily a meta-tyvar
                               --    definitely not a /filled/ meta-tyvar
             -> TcTauType      -- Type 2
             -> TcM Coercion
-- "Unfilled" means that the variable is definitely not a filled-in meta tyvar
--            It might be a skolem, or untouchable, or meta

uUnfilledVar origin t_or_k swapped tv1 ty2
  = do { ty2 <- zonkTcType ty2
             -- Zonk to expose things to the
             -- occurs check, and so that if ty2
             -- looks like a type variable then it
             -- /is/ a type variable
       ; uUnfilledVar1 origin t_or_k swapped tv1 ty2 }

----------
uUnfilledVar1 :: CtOrigin
              -> TypeOrKind
              -> SwapFlag
              -> TcTyVar        -- Tyvar 1: not necessarily a meta-tyvar
                                --    definitely not a /filled/ meta-tyvar
              -> TcTauType      -- Type 2, zonked
              -> TcM Coercion
uUnfilledVar1 origin t_or_k swapped tv1 ty2
  | Just tv2 <- tcGetTyVar_maybe ty2
  = go tv2

  | otherwise
  = uUnfilledVar2 origin t_or_k swapped tv1 ty2

  where
    -- 'go' handles the case where both are
    -- tyvars so we might want to swap
    -- E.g. maybe tv2 is a meta-tyvar and tv1 is not
    go tv2 | tv1 == tv2  -- Same type variable => no-op
           = return (mkNomReflCo (mkTyVarTy tv1))

           | swapOverTyVars False tv1 tv2   -- Distinct type variables
               -- Swap meta tyvar to the left if poss
           = do { tv1 <- zonkTyCoVarKind tv1
                     -- We must zonk tv1's kind because that might
                     -- not have happened yet, and it's an invariant of
                     -- uUnfilledTyVar2 that ty2 is fully zonked
                     -- Omitting this caused #16902
                ; uUnfilledVar2 origin t_or_k (flipSwap swapped)
                           tv2 (mkTyVarTy tv1) }

           | otherwise
           = uUnfilledVar2 origin t_or_k swapped tv1 ty2

----------
uUnfilledVar2 :: CtOrigin
              -> TypeOrKind
              -> SwapFlag
              -> TcTyVar        -- Tyvar 1: not necessarily a meta-tyvar
                                --    definitely not a /filled/ meta-tyvar
              -> TcTauType      -- Type 2, zonked
              -> TcM Coercion
uUnfilledVar2 origin t_or_k swapped tv1 ty2
  = do { dflags  <- getDynFlags
       ; cur_lvl <- getTcLevel
       ; go dflags cur_lvl }
  where
    go dflags cur_lvl
      | canSolveByUnification cur_lvl tv1 ty2
      , MTVU_OK ty2' <- metaTyVarUpdateOK dflags tv1 ty2
      = do { co_k <- uType KindLevel kind_origin (tcTypeKind ty2') (tyVarKind tv1)
           ; traceTc "uUnfilledVar2 ok" $
             vcat [ ppr tv1 <+> dcolon <+> ppr (tyVarKind tv1)
                  , ppr ty2 <+> dcolon <+> ppr (tcTypeKind  ty2)
                  , ppr (isTcReflCo co_k), ppr co_k ]

           ; if isTcReflCo co_k
               -- Only proceed if the kinds match
               -- NB: tv1 should still be unfilled, despite the kind unification
               --     because tv1 is not free in ty2 (or, hence, in its kind)
             then do { writeMetaTyVar tv1 ty2'
                     ; return (mkTcNomReflCo ty2') }

             else defer } -- This cannot be solved now.  See GHC.Tc.Solver.Canonical
                          -- Note [Equalities with incompatible kinds]

      | otherwise
      = do { traceTc "uUnfilledVar2 not ok" (ppr tv1 $$ ppr ty2)
               -- Occurs check or an untouchable: just defer
               -- NB: occurs check isn't necessarily fatal:
               --     eg tv1 occurred in type family parameter
            ; defer }

    ty1 = mkTyVarTy tv1
    kind_origin = KindEqOrigin ty1 (Just ty2) origin (Just t_or_k)

    defer = unSwap swapped (uType_defer t_or_k origin) ty1 ty2

swapOverTyVars :: Bool -> TcTyVar -> TcTyVar -> Bool
swapOverTyVars is_given tv1 tv2
  -- See Note [Unification variables on the left]
  | not is_given, pri1 == 0, pri2 > 0 = True
  | not is_given, pri2 == 0, pri1 > 0 = False

  -- Level comparison: see Note [TyVar/TyVar orientation]
  | lvl1 `strictlyDeeperThan` lvl2 = False
  | lvl2 `strictlyDeeperThan` lvl1 = True

  -- Priority: see Note [TyVar/TyVar orientation]
  | pri1 > pri2 = False
  | pri2 > pri1 = True

  -- Names: see Note [TyVar/TyVar orientation]
  | isSystemName tv2_name, not (isSystemName tv1_name) = True

  | otherwise = False

  where
    lvl1 = tcTyVarLevel tv1
    lvl2 = tcTyVarLevel tv2
    pri1 = lhsPriority tv1
    pri2 = lhsPriority tv2
    tv1_name = Var.varName tv1
    tv2_name = Var.varName tv2


lhsPriority :: TcTyVar -> Int
-- Higher => more important to be on the LHS
--        => more likely to be eliminated
-- See Note [TyVar/TyVar orientation]
lhsPriority tv
  = ASSERT2( isTyVar tv, ppr tv)
    case tcTyVarDetails tv of
      RuntimeUnk  -> 0
      SkolemTv {} -> 0
      MetaTv { mtv_info = info } -> case info of
                                     FlatSkolTv   -> 1
                                     TyVarTv      -> 2
                                     TauTv        -> 3
                                     FlatMetaTv   -> 4
                                     RuntimeUnkTv -> 5

{- Note [TyVar/TyVar orientation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given (a ~ b), should we orient the CTyEqCan as (a~b) or (b~a)?
This is a surprisingly tricky question! This is invariant (TyEq:TV).

The question is answered by swapOverTyVars, which is use
  - in the eager unifier, in GHC.Tc.Utils.Unify.uUnfilledVar1
  - in the constraint solver, in GHC.Tc.Solver.Canonical.canEqTyVarHomo

First note: only swap if you have to!
   See Note [Avoid unnecessary swaps]

So we look for a positive reason to swap, using a three-step test:

* Level comparison. If 'a' has deeper level than 'b',
  put 'a' on the left.  See Note [Deeper level on the left]

* Priority.  If the levels are the same, look at what kind of
  type variable it is, using 'lhsPriority'.

  Generally speaking we always try to put a MetaTv on the left
  in preference to SkolemTv or RuntimeUnkTv:
     a) Because the MetaTv may be touchable and can be unified
     b) Even if it's not touchable, GHC.Tc.Solver.floatEqualities
        looks for meta tyvars on the left

  Tie-breaking rules for MetaTvs:
  - FlatMetaTv = 4: always put on the left.
        See Note [Fmv Orientation Invariant]

        NB: FlatMetaTvs always have the current level, never an
        outer one.  So nothing can be deeper than a FlatMetaTv.

  - TauTv = 3: if we have  tyv_tv ~ tau_tv,
       put tau_tv on the left because there are fewer
       restrictions on updating TauTvs.  Or to say it another
       way, then we won't lose the TyVarTv flag

  - TyVarTv = 2: remember, flat-skols are *only* updated by
       the unflattener, never unified, so TyVarTvs come next

  - FlatSkolTv = 1: put on the left in preference to a SkolemTv.
       See Note [Eliminate flat-skols]

* Names. If the level and priority comparisons are all
  equal, try to eliminate a TyVars with a System Name in
  favour of ones with a Name derived from a user type signature

* Age.  At one point in the past we tried to break any remaining
  ties by eliminating the younger type variable, based on their
  Uniques.  See Note [Eliminate younger unification variables]
  (which also explains why we don't do this any more)

Note [Unification variables on the left]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For wanteds, but not givens, swap (skolem ~ meta-tv) regardless of
level, so that the unification variable is on the left.

* We /don't/ want this for Givens because if we ave
    [G] a[2] ~ alpha[1]
    [W] Bool ~ a[2]
  we want to rewrite the wanted to Bool ~ alpha[1],
  so we can float the constraint and solve it.

* But for Wanteds putting the unification variable on
  the left means an easier job when floating, and when
  reporting errors -- just fewer cases to consider.

  In particular, we get better skolem-escape messages:
  see #18114

Note [Deeper level on the left]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The most important thing is that we want to put tyvars with
the deepest level on the left.  The reason to do so differs for
Wanteds and Givens, but either way, deepest wins!  Simple.

* Wanteds.  Putting the deepest variable on the left maximise the
  chances that it's a touchable meta-tyvar which can be solved.

* Givens. Suppose we have something like
     forall a[2]. b[1] ~ a[2] => beta[1] ~ a[2]

  If we orient the Given a[2] on the left, we'll rewrite the Wanted to
  (beta[1] ~ b[1]), and that can float out of the implication.
  Otherwise it can't.  By putting the deepest variable on the left
  we maximise our changes of eliminating skolem capture.

  See also GHC.Tc.Solver.Monad Note [Let-bound skolems] for another reason
  to orient with the deepest skolem on the left.

  IMPORTANT NOTE: this test does a level-number comparison on
  skolems, so it's important that skolems have (accurate) level
  numbers.

See #15009 for an further analysis of why "deepest on the left"
is a good plan.

Note [Fmv Orientation Invariant]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   * We always orient a constraint
        fmv ~ alpha
     with fmv on the left, even if alpha is
     a touchable unification variable

Reason: doing it the other way round would unify alpha:=fmv, but that
really doesn't add any info to alpha.  But a later constraint alpha ~
Int might unlock everything.  Comment:9 of #12526 gives a detailed
example.

WARNING: I've gone to and fro on this one several times.
I'm now pretty sure that unifying alpha:=fmv is a bad idea!
So orienting with fmvs on the left is a good thing.

This example comes from IndTypesPerfMerge. (Others include
T10226, T10009.)
    From the ambiguity check for
      f :: (F a ~ a) => a
    we get:
          [G] F a ~ a
          [WD] F alpha ~ alpha, alpha ~ a

    From Givens we get
          [G] F a ~ fsk, fsk ~ a

    Now if we flatten we get
          [WD] alpha ~ fmv, F alpha ~ fmv, alpha ~ a

    Now, if we unified alpha := fmv, we'd get
          [WD] F fmv ~ fmv, [WD] fmv ~ a
    And now we are stuck.

So instead the Fmv Orientation Invariant puts the fmv on the
left, giving
      [WD] fmv ~ alpha, [WD] F alpha ~ fmv, [WD] alpha ~ a

    Now we get alpha:=a, and everything works out

Note [Eliminate flat-skols]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have  [G] Num (F [a])
then we flatten to
     [G] Num fsk
     [G] F [a] ~ fsk
where fsk is a flatten-skolem (FlatSkolTv). Suppose we have
      type instance F [a] = a
then we'll reduce the second constraint to
     [G] a ~ fsk
and then replace all uses of 'a' with fsk.  That's bad because
in error messages instead of saying 'a' we'll say (F [a]).  In all
places, including those where the programmer wrote 'a' in the first
place.  Very confusing!  See #7862.

Solution: re-orient a~fsk to fsk~a, so that we preferentially eliminate
the fsk.

Note [Avoid unnecessary swaps]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we swap without actually improving matters, we can get an infinite loop.
Consider
    work item:  a ~ b
   inert item:  b ~ c
We canonicalise the work-item to (a ~ c).  If we then swap it before
adding to the inert set, we'll add (c ~ a), and therefore kick out the
inert guy, so we get
   new work item:  b ~ c
   inert item:     c ~ a
And now the cycle just repeats

Note [Eliminate younger unification variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Given a choice of unifying
     alpha := beta   or   beta := alpha
we try, if possible, to eliminate the "younger" one, as determined
by `ltUnique`.  Reason: the younger one is less likely to appear free in
an existing inert constraint, and hence we are less likely to be forced
into kicking out and rewriting inert constraints.

This is a performance optimisation only.  It turns out to fix
#14723 all by itself, but clearly not reliably so!

It's simple to implement (see nicer_to_update_tv2 in swapOverTyVars).
But, to my surprise, it didn't seem to make any significant difference
to the compiler's performance, so I didn't take it any further.  Still
it seemed to too nice to discard altogether, so I'm leaving these
notes.  SLPJ Jan 18.
-}

-- @trySpontaneousSolve wi@ solves equalities where one side is a
-- touchable unification variable.
-- Returns True <=> spontaneous solve happened
canSolveByUnification :: TcLevel -> TcTyVar -> TcType -> Bool
canSolveByUnification tclvl tv xi
  | isTouchableMetaTyVar tclvl tv
  = case metaTyVarInfo tv of
      TyVarTv -> is_tyvar xi
      _       -> True

  | otherwise    -- Untouchable
  = False
  where
    is_tyvar xi
      = case tcGetTyVar_maybe xi of
          Nothing -> False
          Just tv -> case tcTyVarDetails tv of
                       MetaTv { mtv_info = info }
                                   -> case info of
                                        TyVarTv -> True
                                        _       -> False
                       SkolemTv {} -> True
                       RuntimeUnk  -> True

{- Note [Prevent unification with type families]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We prevent unification with type families because of an uneasy compromise.
It's perfectly sound to unify with type families, and it even improves the
error messages in the testsuite. It also modestly improves performance, at
least in some cases. But it's disastrous for test case perf/compiler/T3064.
Here is the problem: Suppose we have (F ty) where we also have [G] F ty ~ a.
What do we do? Do we reduce F? Or do we use the given? Hard to know what's
best. GHC reduces. This is a disaster for T3064, where the type's size
spirals out of control during reduction. (We're not helped by the fact that
the flattener re-flattens all the arguments every time around.) If we prevent
unification with type families, then the solver happens to use the equality
before expanding the type family.

It would be lovely in the future to revisit this problem and remove this
extra, unnecessary check. But we retain it for now as it seems to work
better in practice.

Note [Refactoring hazard: checkTauTvUpdate]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
I (Richard E.) have a sad story about refactoring this code, retained here
to prevent others (or a future me!) from falling into the same traps.

It all started with #11407, which was caused by the fact that the TyVarTy
case of defer_me didn't look in the kind. But it seemed reasonable to
simply remove the defer_me check instead.

It referred to two Notes (since removed) that were out of date, and the
fast_check code in occurCheckExpand seemed to do just about the same thing as
defer_me. The one piece that defer_me did that wasn't repeated by
occurCheckExpand was the type-family check. (See Note [Prevent unification
with type families].) So I checked the result of occurCheckExpand for any
type family occurrences and deferred if there were any. This was done
in commit e9bf7bb5cc9fb3f87dd05111aa23da76b86a8967 .

This approach turned out not to be performant, because the expanded
type was bigger than the original type, and tyConsOfType (needed to
see if there are any type family occurrences) looks through type
synonyms. So it then struck me that we could dispense with the
defer_me check entirely. This simplified the code nicely, and it cut
the allocations in T5030 by half. But, as documented in Note [Prevent
unification with type families], this destroyed performance in
T3064. Regardless, I missed this regression and the change was
committed as 3f5d1a13f112f34d992f6b74656d64d95a3f506d .

Bottom lines:
 * defer_me is back, but now fixed w.r.t. #11407.
 * Tread carefully before you start to refactor here. There can be
   lots of hard-to-predict consequences.

Note [Type synonyms and the occur check]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Generally speaking we try to update a variable with type synonyms not
expanded, which improves later error messages, unless looking
inside a type synonym may help resolve a spurious occurs check
error. Consider:
          type A a = ()

          f :: (A a -> a -> ()) -> ()
          f = \ _ -> ()

          x :: ()
          x = f (\ x p -> p x)

We will eventually get a constraint of the form t ~ A t. The ok function above will
properly expand the type (A t) to just (), which is ok to be unified with t. If we had
unified with the original type A t, we would lead the type checker into an infinite loop.

Hence, if the occurs check fails for a type synonym application, then (and *only* then),
the ok function expands the synonym to detect opportunities for occurs check success using
the underlying definition of the type synonym.

The same applies later on in the constraint interaction code; see GHC.Tc.Solver.Interact,
function @occ_check_ok@.

Note [Non-TcTyVars in GHC.Tc.Utils.Unify]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Because the same code is now shared between unifying types and unifying
kinds, we sometimes will see proper TyVars floating around the unifier.
Example (from test case polykinds/PolyKinds12):

    type family Apply (f :: k1 -> k2) (x :: k1) :: k2
    type instance Apply g y = g y

When checking the instance declaration, we first *kind-check* the LHS
and RHS, discovering that the instance really should be

    type instance Apply k3 k4 (g :: k3 -> k4) (y :: k3) = g y

During this kind-checking, all the tyvars will be TcTyVars. Then, however,
as a second pass, we desugar the RHS (which is done in functions prefixed
with "tc" in GHC.Tc.TyCl"). By this time, all the kind-vars are proper
TyVars, not TcTyVars, get some kind unification must happen.

Thus, we always check if a TyVar is a TcTyVar before asking if it's a
meta-tyvar.

This used to not be necessary for type-checking (that is, before * :: *)
because expressions get desugared via an algorithm separate from
type-checking (with wrappers, etc.). Types get desugared very differently,
causing this wibble in behavior seen here.
-}

data LookupTyVarResult  -- The result of a lookupTcTyVar call
  = Unfilled TcTyVarDetails     -- SkolemTv or virgin MetaTv
  | Filled   TcType

lookupTcTyVar :: TcTyVar -> TcM LookupTyVarResult
lookupTcTyVar tyvar
  | MetaTv { mtv_ref = ref } <- details
  = do { meta_details <- readMutVar ref
       ; case meta_details of
           Indirect ty -> return (Filled ty)
           Flexi -> do { is_touchable <- isTouchableTcM tyvar
                             -- Note [Unifying untouchables]
                       ; if is_touchable then
                            return (Unfilled details)
                         else
                            return (Unfilled vanillaSkolemTv) } }
  | otherwise
  = return (Unfilled details)
  where
    details = tcTyVarDetails tyvar

{-
Note [Unifying untouchables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We treat an untouchable type variable as if it was a skolem.  That
ensures it won't unify with anything.  It's a slight hack, because
we return a made-up TcTyVarDetails, but I think it works smoothly.
-}

-- | Breaks apart a function kind into its pieces.
matchExpectedFunKind
  :: Outputable fun
  => fun             -- ^ type, only for errors
  -> Arity           -- ^ n: number of desired arrows
  -> TcKind          -- ^ fun_ kind
  -> TcM Coercion    -- ^ co :: fun_kind ~ (arg1 -> ... -> argn -> res)

matchExpectedFunKind hs_ty n k = go n k
  where
    go 0 k = return (mkNomReflCo k)

    go n k | Just k' <- tcView k = go n k'

    go n k@(TyVarTy kvar)
      | isMetaTyVar kvar
      = do { maybe_kind <- readMetaTyVar kvar
           ; case maybe_kind of
                Indirect fun_kind -> go n fun_kind
                Flexi ->             defer n k }

    go n (FunTy { ft_mult = w, ft_arg = arg, ft_res = res })
      = do { co <- go (n-1) res
           ; return (mkTcFunCo Nominal (mkTcNomReflCo w) (mkTcNomReflCo arg) co) }

    go n other
     = defer n other

    defer n k
      = do { arg_kinds <- newMetaKindVars n
           ; res_kind  <- newMetaKindVar
           ; let new_fun = mkVisFunTysMany arg_kinds res_kind
                 origin  = TypeEqOrigin { uo_actual   = k
                                        , uo_expected = new_fun
                                        , uo_thing    = Just (ppr hs_ty)
                                        , uo_visible  = True
                                        }
           ; uType KindLevel origin k new_fun }

{- *********************************************************************
*                                                                      *
                 Occurrence checking
*                                                                      *
********************************************************************* -}


{-  Note [Checking for foralls]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Unless we have -XImpredicativeTypes (which is a totally unsupported
feature), we do not want to unify
    alpha ~ (forall a. a->a) -> Int
So we look for foralls hidden inside the type, and it's convenient
to do that at the same time as the occurs check (which looks for
occurrences of alpha).

However, it's not just a question of looking for foralls /anywhere/!
Consider
   (alpha :: forall k. k->*)  ~  (beta :: forall k. k->*)
This is legal; e.g. dependent/should_compile/T11635.

We don't want to reject it because of the forall in beta's kind, but
(see Note [Occurrence checking: look inside kinds] in GHC.Core.Type)
we do need to look in beta's kind.  So we carry a flag saying if a
'forall' is OK, and switch the flag on when stepping inside a kind.

Why is it OK?  Why does it not count as impredicative polymorphism?
The reason foralls are bad is because we reply on "seeing" foralls
when doing implicit instantiation.  But the forall inside the kind is
fine.  We'll generate a kind equality constraint
  (forall k. k->*) ~ (forall k. k->*)
to check that the kinds of lhs and rhs are compatible.  If alpha's
kind had instead been
  (alpha :: kappa)
then this kind equality would rightly complain about unifying kappa
with (forall k. k->*)

-}

data MetaTyVarUpdateResult a
  = MTVU_OK a
  | MTVU_Bad          -- Forall, predicate, or type family
  | MTVU_HoleBlocker  -- Blocking coercion hole
        -- See Note [Equalities with incompatible kinds] in "GHC.Tc.Solver.Canonical"
  | MTVU_Occurs
    deriving (Functor)

instance Applicative MetaTyVarUpdateResult where
      pure = MTVU_OK
      (<*>) = ap

instance Monad MetaTyVarUpdateResult where
  MTVU_OK x        >>= k = k x
  MTVU_Bad         >>= _ = MTVU_Bad
  MTVU_HoleBlocker >>= _ = MTVU_HoleBlocker
  MTVU_Occurs      >>= _ = MTVU_Occurs

instance Outputable a => Outputable (MetaTyVarUpdateResult a) where
  ppr (MTVU_OK a)      = text "MTVU_OK" <+> ppr a
  ppr MTVU_Bad         = text "MTVU_Bad"
  ppr MTVU_HoleBlocker = text "MTVU_HoleBlocker"
  ppr MTVU_Occurs      = text "MTVU_Occurs"

occCheckForErrors :: DynFlags -> TcTyVar -> Type -> MetaTyVarUpdateResult ()
-- Just for error-message generation; so we return MetaTyVarUpdateResult
-- so the caller can report the right kind of error
-- Check whether
--   a) the given variable occurs in the given type.
--   b) there is a forall in the type (unless we have -XImpredicativeTypes)
occCheckForErrors dflags tv ty
  = case preCheck dflags True tv ty of
      MTVU_OK _        -> MTVU_OK ()
      MTVU_Bad         -> MTVU_Bad
      MTVU_HoleBlocker -> MTVU_HoleBlocker
      MTVU_Occurs      -> case occCheckExpand [tv] ty of
                            Nothing -> MTVU_Occurs
                            Just _  -> MTVU_OK ()

----------------
metaTyVarUpdateOK :: DynFlags
                  -> TcTyVar             -- tv :: k1
                  -> TcType              -- ty :: k2
                  -> MetaTyVarUpdateResult TcType        -- possibly-expanded ty
-- (metaTyVarUpdateOK tv ty)
-- We are about to update the meta-tyvar tv with ty
-- Check (a) that tv doesn't occur in ty (occurs check)
--       (b) that ty does not have any foralls
--           (in the impredicative case), or type functions
--       (c) that ty does not have any blocking coercion holes
--           See Note [Equalities with incompatible kinds] in "GHC.Tc.Solver.Canonical"
--
-- We have two possible outcomes:
-- (1) Return the type to update the type variable with,
--        [we know the update is ok]
-- (2) Return Nothing,
--        [the update might be dodgy]
--
-- Note that "Nothing" does not mean "definite error".  For example
--   type family F a
--   type instance F Int = Int
-- consider
--   a ~ F a
-- This is perfectly reasonable, if we later get a ~ Int.  For now, though,
-- we return Nothing, leaving it to the later constraint simplifier to
-- sort matters out.
--
-- See Note [Refactoring hazard: checkTauTvUpdate]

metaTyVarUpdateOK dflags tv ty
  = case preCheck dflags False tv ty of
         -- False <=> type families not ok
         -- See Note [Prevent unification with type families]
      MTVU_OK _        -> MTVU_OK ty
      MTVU_Bad         -> MTVU_Bad          -- forall, predicate, type function
      MTVU_HoleBlocker -> MTVU_HoleBlocker  -- coercion hole
      MTVU_Occurs      -> case occCheckExpand [tv] ty of
                            Just expanded_ty -> MTVU_OK expanded_ty
                            Nothing          -> MTVU_Occurs

preCheck :: DynFlags -> Bool -> TcTyVar -> TcType -> MetaTyVarUpdateResult ()
-- A quick check for
--   (a) a forall type (forall a. blah)
--   (b) a predicate type (c => ty)
--   (c) a type family; see Note [Prevent unification with type families]
--   (d) a blocking coercion hole
--   (e) an occurrence of the type variable (occurs check)
--
-- For (a), (b), and (c) we check only the top level of the type, NOT
-- inside the kinds of variables it mentions.  For (d) we look deeply
-- in coercions, and for (e) we do look in the kinds of course.

preCheck dflags ty_fam_ok tv ty
  = fast_check ty
  where
    ok :: MetaTyVarUpdateResult ()
    ok = MTVU_OK ()

    -- The GHCi runtime debugger does its type-matching with
    -- unification variables that can unify with a polytype
    -- or a TyCon that would usually be disallowed by bad_tc
    -- See Note [RuntimeUnkTv] in GHC.Runtime.Heap.Inspect
    ghci_tv = case tcTyVarDetails tv of
                MetaTv { mtv_info = RuntimeUnkTv } -> True
                _                                  -> False

    fast_check :: TcType -> MetaTyVarUpdateResult ()
    fast_check (TyVarTy tv')
      | tv == tv' = MTVU_Occurs
      | otherwise = fast_check_occ (tyVarKind tv')
           -- See Note [Occurrence checking: look inside kinds]
           -- in GHC.Core.Type

    fast_check (TyConApp tc tys)
      | bad_tc tc, not ghci_tv = MTVU_Bad
      | otherwise              = mapM fast_check tys >> ok
    fast_check (LitTy {})      = ok
    fast_check (FunTy{ft_af = af, ft_mult = w, ft_arg = a, ft_res = r})
      | InvisArg <- af
      , not ghci_tv            = MTVU_Bad
      | otherwise              = fast_check w   >> fast_check a >> fast_check r
    fast_check (AppTy fun arg) = fast_check fun >> fast_check arg
    fast_check (CastTy ty co)  = fast_check ty  >> fast_check_co co
    fast_check (CoercionTy co) = fast_check_co co
    fast_check (ForAllTy (Bndr tv' _) ty)
       | not ghci_tv = MTVU_Bad
       | tv == tv'   = ok
       | otherwise = do { fast_check_occ (tyVarKind tv')
                        ; fast_check_occ ty }
       -- Under a forall we look only for occurrences of
       -- the type variable

     -- For kinds, we only do an occurs check; we do not worry
     -- about type families or foralls
     -- See Note [Checking for foralls]
    fast_check_occ k | tv `elemVarSet` tyCoVarsOfType k = MTVU_Occurs
                     | otherwise                        = ok

     -- no bother about impredicativity in coercions, as they're
     -- inferred
    fast_check_co co | not (gopt Opt_DeferTypeErrors dflags)
                     , badCoercionHoleCo co            = MTVU_HoleBlocker
        -- Wrinkle (4b) in "GHC.Tc.Solver.Canonical" Note [Equalities with incompatible kinds]

                     | tv `elemVarSet` tyCoVarsOfCo co = MTVU_Occurs
                     | otherwise                       = ok

    bad_tc :: TyCon -> Bool
    bad_tc tc
      | not (isTauTyCon tc)                  = True
      | not (ty_fam_ok || isFamFreeTyCon tc) = True
      | otherwise                            = False
