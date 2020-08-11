{-
%
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

-}

{-# LANGUAGE CPP, TupleSections, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies, DataKinds, TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-} -- Wrinkle in Note [Trees That Grow]
                                      -- in module GHC.Hs.Extension

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns   #-}

module GHC.Tc.Gen.Expr
       ( tcCheckPolyExpr,
         tcCheckMonoExpr, tcCheckMonoExprNC, tcMonoExpr, tcMonoExprNC,
         tcInferSigma, tcInferRho, tcInferRhoNC,
         tcExpr,
         tcSyntaxOp, tcSyntaxOpGen, SyntaxOpType(..), synKnownType,
         tcCheckId,
         addAmbiguousNameErr,
         getFixedTyVars ) where

#include "HsVersions.h"

import GHC.Prelude

import {-# SOURCE #-}   GHC.Tc.Gen.Splice( tcSpliceExpr, tcTypedBracket, tcUntypedBracket )
import GHC.Builtin.Names.TH( liftStringName, liftName )

import GHC.Hs
import GHC.Tc.Utils.Zonk
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Unify
import GHC.Types.Basic
import GHC.Core.Multiplicity
import GHC.Core.UsageEnv
import GHC.Tc.Utils.Instantiate
import GHC.Tc.Gen.Bind        ( chooseInferredQuantifiers, tcLocalBinds )
import GHC.Tc.Gen.Sig         ( tcUserTypeSig, tcInstSig )
import GHC.Tc.Solver          ( simplifyInfer, InferMode(..) )
import GHC.Tc.Instance.Family ( tcGetFamInstEnvs, tcLookupDataFamInst, tcLookupDataFamInst_maybe )
import GHC.Core.FamInstEnv    ( FamInstEnvs )
import GHC.Rename.Env         ( addUsedGRE )
import GHC.Rename.Utils       ( addNameClashErrRn, unknownSubordinateErr )
import GHC.Tc.Utils.Env
import GHC.Tc.Gen.Arrow
import GHC.Tc.Gen.Match
import GHC.Tc.Gen.HsType
import GHC.Tc.TyCl.PatSyn     ( tcPatSynBuilderOcc, nonBidirectionalErr )
import GHC.Tc.Gen.Pat
import GHC.Tc.Utils.TcMType
import GHC.Tc.Types.Origin
import GHC.Tc.Utils.TcType as TcType
import GHC.Types.Id
import GHC.Types.Id.Info
import GHC.Core.ConLike
import GHC.Core.DataCon
import GHC.Core.PatSyn
import GHC.Types.Name
import GHC.Types.Name.Env
import GHC.Types.Name.Set
import GHC.Types.Name.Reader
import GHC.Core.TyCon
import GHC.Core.TyCo.Rep
import GHC.Core.TyCo.Ppr
import GHC.Core.TyCo.Subst (substTyWithInScope)
import GHC.Core.Type
import GHC.Tc.Types.Evidence
import GHC.Types.Var.Set
import GHC.Builtin.Types
import GHC.Builtin.PrimOps( tagToEnumKey )
import GHC.Builtin.Names
import GHC.Driver.Session
import GHC.Types.SrcLoc
import GHC.Utils.Misc
import GHC.Types.Var.Env  ( emptyTidyEnv, mkInScopeSet )
import GHC.Data.List.SetOps
import GHC.Data.Maybe
import GHC.Utils.Outputable as Outputable
import GHC.Data.FastString
import Control.Monad
import GHC.Core.Class(classTyCon)
import GHC.Types.Unique.Set ( nonDetEltsUniqSet )
import qualified GHC.LanguageExtensions as LangExt

import Data.Function
import Data.List (partition, sortBy, groupBy, intersect)
import qualified Data.Set as Set

{-
************************************************************************
*                                                                      *
\subsection{Main wrappers}
*                                                                      *
************************************************************************
-}


tcCheckPolyExpr, tcCheckPolyExprNC
  :: LHsExpr GhcRn         -- Expression to type check
  -> TcSigmaType           -- Expected type (could be a polytype)
  -> TcM (LHsExpr GhcTc) -- Generalised expr with expected type

-- tcCheckPolyExpr is a convenient place (frequent but not too frequent)
-- place to add context information.
-- The NC version does not do so, usually because the caller wants
-- to do so himself.

tcCheckPolyExpr   expr res_ty = tcPolyExpr   expr (mkCheckExpType res_ty)
tcCheckPolyExprNC expr res_ty = tcPolyExprNC expr (mkCheckExpType res_ty)

-- These versions take an ExpType
tcPolyExpr, tcPolyExprNC
  :: LHsExpr GhcRn -> ExpSigmaType
  -> TcM (LHsExpr GhcTc)

tcPolyExpr expr res_ty
  = addExprCtxt expr $
    do { traceTc "tcPolyExpr" (ppr res_ty)
       ; tcPolyExprNC expr res_ty }

tcPolyExprNC (L loc expr) res_ty
  = set_loc_and_ctxt (locA loc) expr $
    do { traceTc "tcPolyExprNC" (ppr res_ty)
       ; (wrap, expr') <- tcSkolemiseET GenSigCtxt res_ty $ \ res_ty ->
                          tcExpr expr res_ty
       ; return $ L loc (mkHsWrap wrap expr') }

  where -- See Note [Rebindable syntax and HsExpansion), which describes
        -- the logic behind this location/context tweaking.
        set_loc_and_ctxt l e m = do
          inGenCode <- inGeneratedCode
          if inGenCode && not (isGeneratedSrcSpan l)
            then setSrcSpan l $ addExprCtxt (L (noAnnSrcSpan l) e) m
            else setSrcSpan l m

---------------
tcInferSigma :: LHsExpr GhcRn -> TcM (LHsExpr GhcTc, TcSigmaType)
-- Used by tcRnExpr to implement GHCi :type
-- It goes against the principle of eager instantiation,
-- so we expect very very few calls to this function
-- Most clients will want tcInferRho
tcInferSigma le@(L loc expr)
  = addExprCtxt le $ setSrcSpanA loc $
    do { (fun, args, ty) <- tcInferApp expr
       ; return (L loc (applyHsArgs fun args), ty) }

---------------
tcCheckMonoExpr, tcCheckMonoExprNC
    :: LHsExpr GhcRn     -- Expression to type check
    -> TcRhoType         -- Expected type
                         -- Definitely no foralls at the top
    -> TcM (LHsExpr GhcTc)
tcCheckMonoExpr   expr res_ty = tcMonoExpr   expr (mkCheckExpType res_ty)
tcCheckMonoExprNC expr res_ty = tcMonoExprNC expr (mkCheckExpType res_ty)

tcMonoExpr, tcMonoExprNC
    :: LHsExpr GhcRn     -- Expression to type check
    -> ExpRhoType        -- Expected type
                         -- Definitely no foralls at the top
    -> TcM (LHsExpr GhcTc)

tcMonoExpr expr res_ty
  = addExprCtxt expr $
    tcMonoExprNC expr res_ty

tcMonoExprNC (L loc expr) res_ty
  = setSrcSpanA loc $
    do  { expr' <- tcExpr expr res_ty
        ; return (L loc expr') }

---------------
tcInferRho, tcInferRhoNC :: LHsExpr GhcRn -> TcM (LHsExpr GhcTc, TcRhoType)
-- Infer a *rho*-type. The return type is always instantiated.
tcInferRho le = addExprCtxt le (tcInferRhoNC le)

tcInferRhoNC (L loc expr)
  = setSrcSpanA loc $
    do { (expr', rho) <- tcInfer (tcExpr expr)
       ; return (L loc expr', rho) }


{- *********************************************************************
*                                                                      *
        tcExpr: the main expression typechecker
*                                                                      *
********************************************************************* -}

tcLExpr, tcLExprNC
    :: LHsExpr GhcRn     -- Expression to type check
    -> ExpRhoType        -- Expected type
                         -- Definitely no foralls at the top
    -> TcM (LHsExpr GhcTc)

tcLExpr expr res_ty
  = setSrcSpanA (getLoc expr) $ addExprCtxt expr (tcLExprNC expr res_ty)

tcLExprNC (L loc expr) res_ty
  = setSrcSpanA loc $
    do  { expr' <- tcExpr expr res_ty
        ; return (L loc expr') }

tcExpr :: HsExpr GhcRn -> ExpRhoType -> TcM (HsExpr GhcTc)
tcExpr (HsVar _ (L _ name))   res_ty = tcCheckId name res_ty
tcExpr e@(HsUnboundVar _ uv)  res_ty = tcUnboundId e uv res_ty

tcExpr e@(HsApp {})     res_ty = tcApp e res_ty
tcExpr e@(HsAppType {}) res_ty = tcApp e res_ty

tcExpr e@(HsLit x lit) res_ty
  = do { let lit_ty = hsLitType lit
       ; tcWrapResult e (HsLit x (convertLit lit)) lit_ty res_ty }

tcExpr (HsPar x expr) res_ty = do { expr' <- tcLExprNC expr res_ty
                                  ; return (HsPar x expr') }

tcExpr (HsPragE x prag expr) res_ty
  = do { expr' <- tcLExpr expr res_ty
       ; return (HsPragE x (tcExprPrag prag) expr') }

tcExpr (HsOverLit x lit) res_ty
  = do  { lit' <- newOverloadedLit lit res_ty
        ; return (HsOverLit x lit') }

tcExpr (NegApp x expr neg_expr) res_ty
  = do  { (expr', neg_expr')
            <- tcSyntaxOp NegateOrigin neg_expr [SynAny] res_ty $
               \[arg_ty] [arg_mult] ->
               tcScalingUsage arg_mult $ tcLExpr expr (mkCheckExpType arg_ty)
        ; return (NegApp x expr' neg_expr') }

tcExpr e@(HsIPVar _ x) res_ty
  = do {   {- Implicit parameters must have a *tau-type* not a
              type scheme.  We enforce this by creating a fresh
              type variable as its type.  (Because res_ty may not
              be a tau-type.) -}
         ip_ty <- newOpenFlexiTyVarTy
       ; let ip_name = mkStrLitTy (hsIPNameFS x)
       ; ipClass <- tcLookupClass ipClassName
       ; ip_var <- emitWantedEvVar origin (mkClassPred ipClass [ip_name, ip_ty])
       ; tcWrapResult e
                   (fromDict ipClass ip_name ip_ty (HsVar noExtField (noLocA ip_var)))
                   ip_ty res_ty }
  where
  -- Coerces a dictionary for `IP "x" t` into `t`.
  fromDict ipClass x ty = mkHsWrap $ mkWpCastR $
                          unwrapIP $ mkClassPred ipClass [x,ty]
  origin = IPOccOrigin x

tcExpr e@(HsOverLabel _ mb_fromLabel l) res_ty
  = do { -- See Note [Type-checking overloaded labels]
         loc <- getSrcSpanM
       ; let loc' = noAnnSrcSpan loc
       ; case mb_fromLabel of
           Just fromLabel -> tcExpr (applyFromLabel loc' fromLabel) res_ty
           Nothing -> do { isLabelClass <- tcLookupClass isLabelClassName
                         ; alpha <- newFlexiTyVarTy liftedTypeKind
                         ; let pred = mkClassPred isLabelClass [lbl, alpha]
                         ; loc <- getSrcSpanM
                         ; var <- emitWantedEvVar origin pred
                         ; tcWrapResult e
                                       (fromDict pred (HsVar noExtField (L (noAnnSrcSpan loc) var)))
                                        alpha res_ty } }
  where
  -- Coerces a dictionary for `IsLabel "x" t` into `t`,
  -- or `HasField "x" r a into `r -> a`.
  fromDict pred = mkHsWrap $ mkWpCastR $ unwrapIP pred
  origin = OverLabelOrigin l
  lbl = mkStrLitTy l

  applyFromLabel :: SrcSpanAnnA -> IdP GhcRn -> HsExpr GhcRn -- AZ Temp
  applyFromLabel loc fromLabel =
    HsAppType NoExtField
         (L loc (HsVar noExtField (L (la2na loc) fromLabel)))
         (mkEmptyWildCardBndrs (L loc (HsTyLit noExtField (HsStrTy NoSourceText l))))

tcExpr (HsLam _ match) res_ty
  = do  { (wrap, match') <- tcMatchLambda herald match_ctxt match res_ty
        ; return (mkHsWrap wrap (HsLam noExtField match')) }
  where
    match_ctxt = MC { mc_what = LambdaExpr, mc_body = tcBody }
    herald = sep [ text "The lambda expression" <+>
                   quotes (pprSetDepth (PartWay 1) $
                           pprMatches match),
                        -- The pprSetDepth makes the abstraction print briefly
                   text "has"]

tcExpr e@(HsLamCase x matches) res_ty
  = do { (wrap, matches')
           <- tcMatchLambda msg match_ctxt matches res_ty
           -- The laziness annotation is because we don't want to fail here
           -- if there are multiple arguments
       ; return (mkHsWrap wrap $ HsLamCase x matches') }
  where
    msg = sep [ text "The function" <+> quotes (ppr e)
              , text "requires"]
    match_ctxt = MC { mc_what = CaseAlt, mc_body = tcBody }

tcExpr e@(ExprWithTySig _ expr hs_ty) res_ty
  = do { (expr', poly_ty) <- tcExprWithSig expr hs_ty
       ; tcWrapResult e expr' poly_ty res_ty }

{-
Note [Type-checking overloaded labels]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Recall that we have

  module GHC.OverloadedLabels where
    class IsLabel (x :: Symbol) a where
      fromLabel :: a

We translate `#foo` to `fromLabel @"foo"`, where we use

 * the in-scope `fromLabel` if `RebindableSyntax` is enabled; or if not
 * `GHC.OverloadedLabels.fromLabel`.

In the `RebindableSyntax` case, the renamer will have filled in the
first field of `HsOverLabel` with the `fromLabel` function to use, and
we simply apply it to the appropriate visible type argument.

In the `OverloadedLabels` case, when we see an overloaded label like
`#foo`, we generate a fresh variable `alpha` for the type and emit an
`IsLabel "foo" alpha` constraint.  Because the `IsLabel` class has a
single method, it is represented by a newtype, so we can coerce
`IsLabel "foo" alpha` to `alpha` (just like for implicit parameters).

-}


{-
************************************************************************
*                                                                      *
                Infix operators and sections
*                                                                      *
************************************************************************

Note [Left sections]
~~~~~~~~~~~~~~~~~~~~
Left sections, like (4 *), are equivalent to
        \ x -> (*) 4 x,
or, if PostfixOperators is enabled, just
        (*) 4
With PostfixOperators we don't actually require the function to take
two arguments at all.  For example, (x `not`) means (not x); you get
postfix operators!  Not Haskell 98, but it's less work and kind of
useful.

Note [Typing rule for ($)]
~~~~~~~~~~~~~~~~~~~~~~~~~~
People write
   runST $ blah
so much, where
   runST :: (forall s. ST s a) -> a
that I have finally given in and written a special type-checking
rule just for saturated applications of ($).
  * Infer the type of the first argument
  * Decompose it; should be of form (arg2_ty -> res_ty),
       where arg2_ty might be a polytype
  * Use arg2_ty to typecheck arg2
-}

tcExpr expr@(OpApp fix arg1 op arg2) res_ty
  | (L loc (HsVar _ (L lv op_name))) <- op
  , op_name `hasKey` dollarIdKey        -- Note [Typing rule for ($)]
  = do { traceTc "Application rule" (ppr op)
       ; (arg1', arg1_ty) <- addErrCtxt (funAppCtxt op arg1 1) $
                             tcInferRhoNC arg1

       ; let doc   = text "The first argument of ($) takes"
             orig1 = lexprCtOrigin arg1
       ; (wrap_arg1, [arg2_sigma], op_res_ty) <-
           matchActualFunTysRho doc orig1 (Just (unLoc arg1)) 1 arg1_ty

       ; mult_wrap <- tcSubMult AppOrigin Many (scaledMult arg2_sigma)
         -- See Note [Wrapper returned from tcSubMult] in GHC.Tc.Utils.Unify.
         --
         -- When ($) becomes multiplicity-polymorphic, then the above check will
         -- need to go. But in the meantime, it would produce ill-typed
         -- desugared code to accept linear functions to the left of a ($).

         -- We have (arg1 $ arg2)
         -- So: arg1_ty = arg2_ty -> op_res_ty
         -- where arg2_sigma maybe polymorphic; that's the point

       ; arg2' <- tcArg nl_op arg2 arg2_sigma 2

       -- Make sure that the argument type has kind '*'
       --   ($) :: forall (r:RuntimeRep) (a:*) (b:TYPE r). (a->b) -> a -> b
       -- Eg we do not want to allow  (D#  $  4.0#)   #5570
       --    (which gives a seg fault)
       ; _ <- unifyKind (Just (XHsType $ NHsCoreTy (scaledThing arg2_sigma)))
                        (tcTypeKind (scaledThing arg2_sigma)) liftedTypeKind
           -- Ignore the evidence. arg2_sigma must have type * or #,
           -- because we know (arg2_sigma -> op_res_ty) is well-kinded
           -- (because otherwise matchActualFunTysRho would fail)
           -- So this 'unifyKind' will either succeed with Refl, or will
           -- produce an insoluble constraint * ~ #, which we'll report later.

       -- NB: unlike the argument type, the *result* type, op_res_ty can
       -- have any kind (#8739), so we don't need to check anything for that

       ; op_id  <- tcLookupId op_name
       ; let op' = L loc (mkHsWrap (mkWpTyApps [ getRuntimeRep op_res_ty
                                               , scaledThing arg2_sigma
                                               , op_res_ty])
                                   (HsVar noExtField (L lv op_id)))
             -- arg1' :: arg1_ty
             -- wrap_arg1 :: arg1_ty "->" (arg2_sigma -> op_res_ty)
             -- op' :: (a2_ty -> op_res_ty) -> a2_ty -> op_res_ty

             expr' = OpApp fix (mkLHsWrap (wrap_arg1 <.> mult_wrap) arg1') op' arg2'

       ; tcWrapResult expr expr' op_res_ty res_ty }

  | L loc (HsRecFld _ (Ambiguous _ lbl)) <- op
  , Just sig_ty <- obviousSig (unLoc arg1)
    -- See Note [Disambiguating record fields]
  = do { sig_tc_ty <- tcHsSigWcType ExprSigCtxt sig_ty
       ; sel_name <- disambiguateSelector lbl sig_tc_ty
       ; let op' = L loc (HsRecFld noExtField (Unambiguous sel_name lbl))
       ; tcExpr (OpApp fix arg1 op' arg2) res_ty
       }

  | otherwise
  = do { traceTc "Non Application rule" (ppr op)
       ; (op', op_ty) <- tcInferRhoNC op

       ; (wrap_fun, [arg1_ty, arg2_ty], op_res_ty)
                  <- matchActualFunTysRho (mk_op_msg op) fn_orig
                                          (Just (unLoc op)) 2 op_ty
         -- You might think we should use tcInferApp here, but there is
         -- too much impedance-matching, because tcApp may return wrappers as
         -- well as type-checked arguments.

       ; arg1' <- tcArg nl_op arg1 arg1_ty 1
       ; arg2' <- tcArg nl_op arg2 arg2_ty 2

       ; let expr' = OpApp fix arg1' (mkLHsWrap wrap_fun op') arg2'
       ; tcWrapResult expr expr' op_res_ty res_ty }
  where
    fn_orig = exprCtOrigin nl_op
    nl_op   = unLoc op

-- Right sections, equivalent to \ x -> x `op` expr, or
--      \ x -> op x expr

tcExpr expr@(SectionR x op arg2) res_ty
  = do { (op', op_ty) <- tcInferRhoNC op
       ; (wrap_fun, [Scaled arg1_mult arg1_ty, arg2_ty], op_res_ty)
                  <- matchActualFunTysRho (mk_op_msg op) fn_orig
                                          (Just (unLoc op)) 2 op_ty
       ; arg2' <- tcArg (unLoc op) arg2 arg2_ty 2
       ; let expr'      = SectionR x (mkLHsWrap wrap_fun op') arg2'
             act_res_ty = mkVisFunTy arg1_mult arg1_ty op_res_ty
       ; tcWrapResultMono expr expr' act_res_ty res_ty }

  where
    fn_orig = lexprCtOrigin op
    -- It's important to use the origin of 'op', so that call-stacks
    -- come out right; they are driven by the OccurrenceOf CtOrigin
    -- See #13285

tcExpr expr@(SectionL x arg1 op) res_ty
  = do { (op', op_ty) <- tcInferRhoNC op
       ; dflags <- getDynFlags      -- Note [Left sections]
       ; let n_reqd_args | xopt LangExt.PostfixOperators dflags = 1
                         | otherwise                            = 2

       ; (wrap_fn, (arg1_ty:arg_tys), op_res_ty)
           <- matchActualFunTysRho (mk_op_msg op) fn_orig
                                   (Just (unLoc op)) n_reqd_args op_ty
       ; arg1' <- tcArg (unLoc op) arg1 arg1_ty 1
       ; let expr'      = SectionL x arg1' (mkLHsWrap wrap_fn op')
             act_res_ty = mkVisFunTys arg_tys op_res_ty
       ; tcWrapResultMono expr expr' act_res_ty res_ty }
  where
    fn_orig = lexprCtOrigin op
    -- It's important to use the origin of 'op', so that call-stacks
    -- come out right; they are driven by the OccurrenceOf CtOrigin
    -- See #13285

tcExpr expr@(ExplicitTuple x tup_args boxity) res_ty
  | all tupArgPresent tup_args
  = do { let arity  = length tup_args
             tup_tc = tupleTyCon boxity arity
               -- NB: tupleTyCon doesn't flatten 1-tuples
               -- See Note [Don't flatten tuples from HsSyn] in GHC.Core.Make
       ; res_ty <- expTypeToType res_ty
       ; (coi, arg_tys) <- matchExpectedTyConApp tup_tc res_ty
                           -- Unboxed tuples have RuntimeRep vars, which we
                           -- don't care about here
                           -- See Note [Unboxed tuple RuntimeRep vars] in GHC.Core.TyCon
       ; let arg_tys' = case boxity of Unboxed -> drop arity arg_tys
                                       Boxed   -> arg_tys
       ; tup_args1 <- tcTupArgs tup_args arg_tys'
       ; return $ mkHsWrapCo coi (ExplicitTuple x tup_args1 boxity) }

  | otherwise
  = -- The tup_args are a mixture of Present and Missing (for tuple sections)
    do { let arity = length tup_args

       ; arg_tys <- case boxity of
           { Boxed   -> newFlexiTyVarTys arity liftedTypeKind
           ; Unboxed -> replicateM arity newOpenFlexiTyVarTy }

       -- Handle tuple sections where
       ; tup_args1 <- tcTupArgs tup_args arg_tys

       ; let expr'       = ExplicitTuple x tup_args1 boxity
             missing_tys = [Scaled mult ty | (L _ (Missing (Scaled mult _)), ty) <- zip tup_args1 arg_tys]

             -- See Note [Linear fields generalization]
             act_res_ty
                 = mkVisFunTys missing_tys (mkTupleTy1 boxity arg_tys)
                   -- See Note [Don't flatten tuples from HsSyn] in GHC.Core.Make

       ; traceTc "ExplicitTuple" (ppr act_res_ty $$ ppr res_ty)

       ; tcWrapResultMono expr expr' act_res_ty res_ty }

tcExpr (ExplicitSum _ alt arity expr) res_ty
  = do { let sum_tc = sumTyCon arity
       ; res_ty <- expTypeToType res_ty
       ; (coi, arg_tys) <- matchExpectedTyConApp sum_tc res_ty
       ; -- Drop levity vars, we don't care about them here
         let arg_tys' = drop arity arg_tys
       ; expr' <- tcCheckPolyExpr expr (arg_tys' `getNth` (alt - 1))
       ; return $ mkHsWrapCo coi (ExplicitSum arg_tys' alt arity expr' ) }

-- This will see the empty list only when -XOverloadedLists.
-- See Note [Empty lists] in GHC.Hs.Expr.
tcExpr (ExplicitList _ witness exprs) res_ty
  = case witness of
      Nothing   -> do  { res_ty <- expTypeToType res_ty
                       ; (coi, elt_ty) <- matchExpectedListTy res_ty
                       ; exprs' <- mapM (tc_elt elt_ty) exprs
                       ; return $
                         mkHsWrapCo coi $ ExplicitList elt_ty Nothing exprs' }

      Just fln -> do { ((exprs', elt_ty), fln')
                         <- tcSyntaxOp ListOrigin fln
                                       [synKnownType intTy, SynList] res_ty $
                            \ [elt_ty] [_int_mul, list_mul] ->
                              -- We ignore _int_mul because the integer (first
                              -- argument of fromListN) is statically known: it
                              -- is desugared to a literal. Therefore there is
                              -- no variable of which to scale the usage in that
                              -- first argument, and `_int_mul` is completely
                              -- free in this expression.
                            do { exprs' <-
                                    mapM (tcScalingUsage list_mul . tc_elt elt_ty) exprs
                               ; return (exprs', elt_ty) }

                     ; return $ ExplicitList elt_ty (Just fln') exprs' }
     where tc_elt elt_ty expr = tcCheckPolyExpr expr elt_ty

{-
************************************************************************
*                                                                      *
                Let, case, if, do
*                                                                      *
************************************************************************
-}

tcExpr (HsLet x binds expr) res_ty
  = do  { (binds', expr') <- tcLocalBinds binds $
                             tcLExpr expr res_ty
        ; return (HsLet x binds' expr') }

tcExpr (HsCase x scrut matches) res_ty
  = do  {  -- We used to typecheck the case alternatives first.
           -- The case patterns tend to give good type info to use
           -- when typechecking the scrutinee.  For example
           --   case (map f) of
           --     (x:xs) -> ...
           -- will report that map is applied to too few arguments
           --
           -- But now, in the GADT world, we need to typecheck the scrutinee
           -- first, to get type info that may be refined in the case alternatives
          let mult = Many
            -- There is not yet syntax or inference mechanism for case
            -- expressions to be anything else than unrestricted.

          -- Typecheck the scrutinee.  We use tcInferRho but tcInferSigma
          -- would also be possible (tcMatchesCase accepts sigma-types)
          -- Interesting litmus test: do these two behave the same?
          --     case id        of {..}
          --     case (\v -> v) of {..}
          -- This design choice is discussed in #17790
        ; (scrut', scrut_ty) <- tcScalingUsage mult $ tcInferRho scrut

        ; traceTc "HsCase" (ppr scrut_ty)
        ; matches' <- tcMatchesCase match_ctxt (Scaled mult scrut_ty) matches res_ty
        ; return (HsCase x scrut' matches') }
 where
    match_ctxt = MC { mc_what = CaseAlt,
                      mc_body = tcBody }

tcExpr (HsIf x pred b1 b2) res_ty
  = do { pred' <- tcLExpr pred (mkCheckExpType boolTy)
       ; (u1,b1') <- tcCollectingUsage $ tcLExpr b1 res_ty
       ; (u2,b2') <- tcCollectingUsage $ tcLExpr b2 res_ty
       ; tcEmitBindingUsage (supUE u1 u2)
       ; return (HsIf x pred' b1' b2') }

tcExpr (HsMultiIf _ alts) res_ty
  = do { alts' <- mapM (wrapLocM $ tcGRHS match_ctxt res_ty) alts
       ; res_ty <- readExpType res_ty
       ; return (HsMultiIf res_ty alts') }
  where match_ctxt = MC { mc_what = IfAlt, mc_body = tcBody }

tcExpr (HsDo _ do_or_lc stmts) res_ty
  = do { expr' <- tcDoStmts do_or_lc stmts res_ty
       ; return expr' }

tcExpr (HsProc x pat cmd) res_ty
  = do  { (pat', cmd', coi) <- tcProc pat cmd res_ty
        ; return $ mkHsWrapCo coi (HsProc x pat' cmd') }

-- Typechecks the static form and wraps it with a call to 'fromStaticPtr'.
-- See Note [Grand plan for static forms] in GHC.Iface.Tidy.StaticPtrTable for an overview.
-- To type check
--      (static e) :: p a
-- we want to check (e :: a),
-- and wrap (static e) in a call to
--    fromStaticPtr :: IsStatic p => StaticPtr a -> p a

tcExpr (HsStatic fvs expr) res_ty
  = do  { res_ty          <- expTypeToType res_ty
        ; (co, (p_ty, expr_ty)) <- matchExpectedAppTy res_ty
        ; (expr', lie)    <- captureConstraints $
            addErrCtxt (hang (text "In the body of a static form:")
                             2 (ppr expr)
                       ) $
            tcCheckPolyExprNC expr expr_ty

        -- Check that the free variables of the static form are closed.
        -- It's OK to use nonDetEltsUniqSet here as the only side effects of
        -- checkClosedInStaticForm are error messages.
        ; mapM_ checkClosedInStaticForm $ nonDetEltsUniqSet fvs

        -- Require the type of the argument to be Typeable.
        -- The evidence is not used, but asking the constraint ensures that
        -- the current implementation is as restrictive as future versions
        -- of the StaticPointers extension.
        ; typeableClass <- tcLookupClass typeableClassName
        ; _ <- emitWantedEvVar StaticOrigin $
                  mkTyConApp (classTyCon typeableClass)
                             [liftedTypeKind, expr_ty]

        -- Insert the constraints of the static form in a global list for later
        -- validation.
        ; emitStaticConstraints lie

        -- Wrap the static form with the 'fromStaticPtr' call.
        ; fromStaticPtr <- newMethodFromName StaticOrigin fromStaticPtrName
                                             [p_ty]
        ; let wrap = mkWpTyApps [expr_ty]
        ; loc <- getSrcSpanM
        ; return $ mkHsWrapCo co $ HsApp noComments
                            (L (noAnnSrcSpan loc) $ mkHsWrap wrap fromStaticPtr)
                            (L (noAnnSrcSpan loc) (HsStatic fvs expr'))
        }

{-
************************************************************************
*                                                                      *
                Record construction and update
*                                                                      *
************************************************************************
-}

tcExpr expr@(RecordCon { rcon_con_name = L loc con_name
                       , rcon_flds = rbinds }) res_ty
  = do  { con_like <- tcLookupConLike con_name

        -- Check for missing fields
        ; checkMissingFields con_like rbinds

        ; (con_expr, con_sigma) <- tcInferId con_name
        ; (con_wrap, con_tau)   <- topInstantiate orig con_sigma
              -- a shallow instantiation should really be enough for
              -- a data constructor.
        ; let arity = conLikeArity con_like
              Right (arg_tys, actual_res_ty) = tcSplitFunTysN arity con_tau
        ; case conLikeWrapId_maybe con_like of {
               Nothing -> nonBidirectionalErr (conLikeName con_like) ;
               Just con_id ->

     do { rbinds' <- tcRecordBinds con_like (map scaledThing arg_tys) rbinds
                   -- It is currently not possible for a record to have
                   -- multiplicities. When they do, `tcRecordBinds` will take
                   -- scaled types instead. Meanwhile, it's safe to take
                   -- `scaledThing` above, as we know all the multiplicities are
                   -- Many.
        ; let rcon_tc = RecordConTc
                           { rcon_con_like = con_like
                           , rcon_con_expr = mkHsWrap con_wrap con_expr }
              expr' = RecordCon { rcon_ext = rcon_tc
                                , rcon_con_name = L loc con_id
                                , rcon_flds = rbinds' }

        ; tcWrapResultMono expr expr' actual_res_ty res_ty } } }
  where
    orig = OccurrenceOf con_name

{-
Note [Type of a record update]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The main complication with RecordUpd is that we need to explicitly
handle the *non-updated* fields.  Consider:

        data T a b c = MkT1 { fa :: a, fb :: (b,c) }
                     | MkT2 { fa :: a, fb :: (b,c), fc :: c -> c }
                     | MkT3 { fd :: a }

        upd :: T a b c -> (b',c) -> T a b' c
        upd t x = t { fb = x}

The result type should be (T a b' c)
not (T a b c),   because 'b' *is not* mentioned in a non-updated field
not (T a b' c'), because 'c' *is*     mentioned in a non-updated field
NB that it's not good enough to look at just one constructor; we must
look at them all; cf #3219

After all, upd should be equivalent to:
        upd t x = case t of
                        MkT1 p q -> MkT1 p x
                        MkT2 a b -> MkT2 p b
                        MkT3 d   -> error ...

So we need to give a completely fresh type to the result record,
and then constrain it by the fields that are *not* updated ("p" above).
We call these the "fixed" type variables, and compute them in getFixedTyVars.

Note that because MkT3 doesn't contain all the fields being updated,
its RHS is simply an error, so it doesn't impose any type constraints.
Hence the use of 'relevant_cont'.

Note [Implicit type sharing]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
We also take into account any "implicit" non-update fields.  For example
        data T a b where { MkT { f::a } :: T a a; ... }
So the "real" type of MkT is: forall ab. (a~b) => a -> T a b

Then consider
        upd t x = t { f=x }
We infer the type
        upd :: T a b -> a -> T a b
        upd (t::T a b) (x::a)
           = case t of { MkT (co:a~b) (_:a) -> MkT co x }
We can't give it the more general type
        upd :: T a b -> c -> T c b

Note [Criteria for update]
~~~~~~~~~~~~~~~~~~~~~~~~~~
We want to allow update for existentials etc, provided the updated
field isn't part of the existential. For example, this should be ok.
  data T a where { MkT { f1::a, f2::b->b } :: T a }
  f :: T a -> b -> T b
  f t b = t { f1=b }

The criterion we use is this:

  The types of the updated fields
  mention only the universally-quantified type variables
  of the data constructor

NB: this is not (quite) the same as being a "naughty" record selector
(See Note [Naughty record selectors]) in GHC.Tc.TyCl), at least
in the case of GADTs. Consider
   data T a where { MkT :: { f :: a } :: T [a] }
Then f is not "naughty" because it has a well-typed record selector.
But we don't allow updates for 'f'.  (One could consider trying to
allow this, but it makes my head hurt.  Badly.  And no one has asked
for it.)

In principle one could go further, and allow
  g :: T a -> T a
  g t = t { f2 = \x -> x }
because the expression is polymorphic...but that seems a bridge too far.

Note [Data family example]
~~~~~~~~~~~~~~~~~~~~~~~~~~
    data instance T (a,b) = MkT { x::a, y::b }
  --->
    data :TP a b = MkT { a::a, y::b }
    coTP a b :: T (a,b) ~ :TP a b

Suppose r :: T (t1,t2), e :: t3
Then  r { x=e } :: T (t3,t1)
  --->
      case r |> co1 of
        MkT x y -> MkT e y |> co2
      where co1 :: T (t1,t2) ~ :TP t1 t2
            co2 :: :TP t3 t2 ~ T (t3,t2)
The wrapping with co2 is done by the constructor wrapper for MkT

Outgoing invariants
~~~~~~~~~~~~~~~~~~~
In the outgoing (HsRecordUpd scrut binds cons in_inst_tys out_inst_tys):

  * cons are the data constructors to be updated

  * in_inst_tys, out_inst_tys have same length, and instantiate the
        *representation* tycon of the data cons.  In Note [Data
        family example], in_inst_tys = [t1,t2], out_inst_tys = [t3,t2]

Note [Mixed Record Field Updates]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider the following pattern synonym.

  data MyRec = MyRec { foo :: Int, qux :: String }

  pattern HisRec{f1, f2} = MyRec{foo = f1, qux=f2}

This allows updates such as the following

  updater :: MyRec -> MyRec
  updater a = a {f1 = 1 }

It would also make sense to allow the following update (which we reject).

  updater a = a {f1 = 1, qux = "two" } ==? MyRec 1 "two"

This leads to confusing behaviour when the selectors in fact refer the same
field.

  updater a = a {f1 = 1, foo = 2} ==? ???

For this reason, we reject a mixture of pattern synonym and normal record
selectors in the same update block. Although of course we still allow the
following.

  updater a = (a {f1 = 1}) {foo = 2}

  > updater (MyRec 0 "str")
  MyRec 2 "str"

-}

tcExpr expr@(RecordUpd { rupd_expr = record_expr, rupd_flds = rbnds }) res_ty
  = ASSERT( notNull rbnds )
    do  { -- STEP -2: typecheck the record_expr, the record to be updated
          (record_expr', record_rho) <- tcScalingUsage Many $ tcInferRho record_expr
            -- Record update drops some of the content of the record (namely the
            -- content of the field being updated). As a consequence, unless the
            -- field being updated is unrestricted in the record, or we need an
            -- unrestricted record. Currently, we simply always require an
            -- unrestricted record.
            --
            -- Consider the following example:
            --
            -- data R a = R { self :: a }
            -- bad :: a ⊸ ()
            -- bad x = let r = R x in case r { self = () } of { R x' -> x' }
            --
            -- This should definitely *not* typecheck.

        -- STEP -1  See Note [Disambiguating record fields]
        -- After this we know that rbinds is unambiguous
        ; rbinds <- disambiguateRecordBinds record_expr record_rho rbnds res_ty
        ; let upd_flds = map (unLoc . hsRecFieldLbl . unLoc) rbinds
              upd_fld_occs = map (occNameFS . rdrNameOcc . rdrNameAmbiguousFieldOcc) upd_flds
              sel_ids      = map selectorAmbiguousFieldOcc upd_flds
        -- STEP 0
        -- Check that the field names are really field names
        -- and they are all field names for proper records or
        -- all field names for pattern synonyms.
        ; let bad_guys = [ setSrcSpan loc $ addErrTc (notSelector fld_name)
                         | fld <- rbinds,
                           -- Excludes class ops
                           let L loc sel_id = hsRecUpdFieldId (unLoc fld),
                           not (isRecordSelector sel_id),
                           let fld_name = idName sel_id ]
        ; unless (null bad_guys) (sequence bad_guys >> failM)
        -- See note [Mixed Record Selectors]
        ; let (data_sels, pat_syn_sels) =
                partition isDataConRecordSelector sel_ids
        ; MASSERT( all isPatSynRecordSelector pat_syn_sels )
        ; checkTc ( null data_sels || null pat_syn_sels )
                  ( mixedSelectors data_sels pat_syn_sels )

        -- STEP 1
        -- Figure out the tycon and data cons from the first field name
        ; let   -- It's OK to use the non-tc splitters here (for a selector)
              sel_id : _  = sel_ids

              mtycon :: Maybe TyCon
              mtycon = case idDetails sel_id of
                          RecSelId (RecSelData tycon) _ -> Just tycon
                          _ -> Nothing

              con_likes :: [ConLike]
              con_likes = case idDetails sel_id of
                             RecSelId (RecSelData tc) _
                                -> map RealDataCon (tyConDataCons tc)
                             RecSelId (RecSelPatSyn ps) _
                                -> [PatSynCon ps]
                             _  -> panic "tcRecordUpd"
                -- NB: for a data type family, the tycon is the instance tycon

              relevant_cons = conLikesWithFields con_likes upd_fld_occs
                -- A constructor is only relevant to this process if
                -- it contains *all* the fields that are being updated
                -- Other ones will cause a runtime error if they occur

        -- Step 2
        -- Check that at least one constructor has all the named fields
        -- i.e. has an empty set of bad fields returned by badFields
        ; checkTc (not (null relevant_cons)) (badFieldsUpd rbinds con_likes)

        -- Take apart a representative constructor
        ; let con1 = ASSERT( not (null relevant_cons) ) head relevant_cons
              (con1_tvs, _, _, _prov_theta, req_theta, scaled_con1_arg_tys, _)
                 = conLikeFullSig con1
              con1_arg_tys = map scaledThing scaled_con1_arg_tys
                -- We can safely drop the fields' multiplicities because
                -- they are currently always 1: there is no syntax for record
                -- fields with other multiplicities yet. This way we don't need
                -- to handle it in the rest of the function
              con1_flds   = map flLabel $ conLikeFieldLabels con1
              con1_tv_tys = mkTyVarTys con1_tvs
              con1_res_ty = case mtycon of
                              Just tc -> mkFamilyTyConApp tc con1_tv_tys
                              Nothing -> conLikeResTy con1 con1_tv_tys

        -- Check that we're not dealing with a unidirectional pattern
        -- synonym
        ; unless (isJust $ conLikeWrapId_maybe con1)
                  (nonBidirectionalErr (conLikeName con1))

        -- STEP 3    Note [Criteria for update]
        -- Check that each updated field is polymorphic; that is, its type
        -- mentions only the universally-quantified variables of the data con
        ; let flds1_w_tys  = zipEqual "tcExpr:RecConUpd" con1_flds con1_arg_tys
              bad_upd_flds = filter bad_fld flds1_w_tys
              con1_tv_set  = mkVarSet con1_tvs
              bad_fld (fld, ty) = fld `elem` upd_fld_occs &&
                                      not (tyCoVarsOfType ty `subVarSet` con1_tv_set)
        ; checkTc (null bad_upd_flds) (badFieldTypes bad_upd_flds)

        -- STEP 4  Note [Type of a record update]
        -- Figure out types for the scrutinee and result
        -- Both are of form (T a b c), with fresh type variables, but with
        -- common variables where the scrutinee and result must have the same type
        -- These are variables that appear in *any* arg of *any* of the
        -- relevant constructors *except* in the updated fields
        --
        ; let fixed_tvs = getFixedTyVars upd_fld_occs con1_tvs relevant_cons
              is_fixed_tv tv = tv `elemVarSet` fixed_tvs

              mk_inst_ty :: TCvSubst -> (TyVar, TcType) -> TcM (TCvSubst, TcType)
              -- Deals with instantiation of kind variables
              --   c.f. GHC.Tc.Utils.TcMType.newMetaTyVars
              mk_inst_ty subst (tv, result_inst_ty)
                | is_fixed_tv tv   -- Same as result type
                = return (extendTvSubst subst tv result_inst_ty, result_inst_ty)
                | otherwise        -- Fresh type, of correct kind
                = do { (subst', new_tv) <- newMetaTyVarX subst tv
                     ; return (subst', mkTyVarTy new_tv) }

        ; (result_subst, con1_tvs') <- newMetaTyVars con1_tvs
        ; let result_inst_tys = mkTyVarTys con1_tvs'
              init_subst = mkEmptyTCvSubst (getTCvInScope result_subst)

        ; (scrut_subst, scrut_inst_tys) <- mapAccumLM mk_inst_ty init_subst
                                                      (con1_tvs `zip` result_inst_tys)

        ; let rec_res_ty    = TcType.substTy result_subst con1_res_ty
              scrut_ty      = TcType.substTy scrut_subst  con1_res_ty
              con1_arg_tys' = map (TcType.substTy result_subst) con1_arg_tys

        ; co_scrut <- unifyType (Just (unLoc record_expr)) record_rho scrut_ty
                -- NB: normal unification is OK here (as opposed to subsumption),
                -- because for this to work out, both record_rho and scrut_ty have
                -- to be normal datatypes -- no contravariant stuff can go on

        -- STEP 5
        -- Typecheck the bindings
        ; rbinds'      <- tcRecordUpd con1 con1_arg_tys' rbinds

        -- STEP 6: Deal with the stupid theta
        ; let theta' = substThetaUnchecked scrut_subst (conLikeStupidTheta con1)
        ; instStupidTheta RecordUpdOrigin theta'

        -- Step 7: make a cast for the scrutinee, in the
        --         case that it's from a data family
        ; let fam_co :: HsWrapper   -- RepT t1 .. tn ~R scrut_ty
              fam_co | Just tycon <- mtycon
                     , Just co_con <- tyConFamilyCoercion_maybe tycon
                     = mkWpCastR (mkTcUnbranchedAxInstCo co_con scrut_inst_tys [])
                     | otherwise
                     = idHsWrapper

        -- Step 8: Check that the req constraints are satisfied
        -- For normal data constructors req_theta is empty but we must do
        -- this check for pattern synonyms.
        ; let req_theta' = substThetaUnchecked scrut_subst req_theta
        ; req_wrap <- instCallConstraints RecordUpdOrigin req_theta'

        -- Phew!
        ; let upd_tc = RecordUpdTc { rupd_cons = relevant_cons
                                   , rupd_in_tys = scrut_inst_tys
                                   , rupd_out_tys = result_inst_tys
                                   , rupd_wrap = req_wrap }
              expr' = RecordUpd { rupd_expr = mkLHsWrap fam_co $
                                              mkLHsWrapCo co_scrut record_expr'
                                , rupd_flds = rbinds'
                                , rupd_ext = upd_tc }

        ; tcWrapResult expr expr' rec_res_ty res_ty }

tcExpr e@(HsRecFld _ f) res_ty
    = tcCheckRecSelId e f res_ty

{-
************************************************************************
*                                                                      *
        Arithmetic sequences                    e.g. [a,b..]
        and their parallel-array counterparts   e.g. [: a,b.. :]

*                                                                      *
************************************************************************
-}

tcExpr (ArithSeq _ witness seq) res_ty
  = tcArithSeq witness seq res_ty

{-
************************************************************************
*                                                                      *
                Template Haskell
*                                                                      *
************************************************************************
-}

-- HsSpliced is an annotation produced by 'GHC.Rename.Splice.rnSpliceExpr'.
-- Here we get rid of it and add the finalizers to the global environment.
--
-- See Note [Delaying modFinalizers in untyped splices] in GHC.Rename.Splice.
tcExpr (HsSpliceE _ (HsSpliced _ mod_finalizers (HsSplicedExpr expr)))
       res_ty
  = do addModFinalizersWithLclEnv mod_finalizers
       tcExpr expr res_ty
tcExpr (HsSpliceE _ splice)          res_ty = tcSpliceExpr splice res_ty
tcExpr e@(HsBracket _ brack)         res_ty = tcTypedBracket e brack res_ty
tcExpr e@(HsRnBracketOut _ brack ps) res_ty = tcUntypedBracket e brack ps res_ty

{-
************************************************************************
*                                                                      *
                Rebindable syntax
*                                                                      *
************************************************************************
-}

-- See Note [Rebindable syntax and HsExpansion].
tcExpr (XExpr (HsExpanded a b)) t
  = fmap (XExpr . ExpansionExpr . HsExpanded a) $
      setSrcSpan generatedSrcSpan (tcExpr b t)

{-
************************************************************************
*                                                                      *
                Catch-all
*                                                                      *
************************************************************************
-}

tcExpr other _ = pprPanic "tcLExpr" (ppr other)
  -- Include ArrForm, ArrApp, which shouldn't appear at all
  -- Also HsTcBracketOut, HsQuasiQuoteE


{- *********************************************************************
*                                                                      *
             Pragmas on expressions
*                                                                      *
********************************************************************* -}

tcExprPrag :: HsPragE GhcRn -> HsPragE GhcTc
tcExprPrag (HsPragSCC x1 src ann) = HsPragSCC x1 src ann
tcExprPrag (HsPragTick x1 src info srcInfo) = HsPragTick x1 src info srcInfo


{- *********************************************************************
*                                                                      *
             Expression with type signature e::ty
*                                                                      *
********************************************************************* -}

tcExprWithSig :: LHsExpr GhcRn -> LHsSigWcType (NoGhcTc GhcRn)
              -> TcM (HsExpr GhcTc, TcSigmaType)
tcExprWithSig expr hs_ty
  = do { sig_info <- checkNoErrs $  -- Avoid error cascade
                     tcUserTypeSig loc hs_ty Nothing
       ; (expr', poly_ty) <- tcExprSig expr sig_info
       ; return (ExprWithTySig noExtField expr' hs_ty, poly_ty) }
  where
    loc = getLocA (hsSigWcType hs_ty)

{-
************************************************************************
*                                                                      *
                Arithmetic sequences [a..b] etc
*                                                                      *
************************************************************************
-}

tcArithSeq :: Maybe (SyntaxExpr GhcRn) -> ArithSeqInfo GhcRn -> ExpRhoType
           -> TcM (HsExpr GhcTc)

tcArithSeq witness seq@(From expr) res_ty
  = do { (wrap, elt_mult, elt_ty, wit') <- arithSeqEltType witness res_ty
       ; expr' <-tcScalingUsage elt_mult $ tcCheckPolyExpr expr elt_ty
       ; enum_from <- newMethodFromName (ArithSeqOrigin seq)
                              enumFromName [elt_ty]
       ; return $ mkHsWrap wrap $
         ArithSeq enum_from wit' (From expr') }

tcArithSeq witness seq@(FromThen expr1 expr2) res_ty
  = do { (wrap, elt_mult, elt_ty, wit') <- arithSeqEltType witness res_ty
       ; expr1' <- tcScalingUsage elt_mult $ tcCheckPolyExpr expr1 elt_ty
       ; expr2' <- tcScalingUsage elt_mult $ tcCheckPolyExpr expr2 elt_ty
       ; enum_from_then <- newMethodFromName (ArithSeqOrigin seq)
                              enumFromThenName [elt_ty]
       ; return $ mkHsWrap wrap $
         ArithSeq enum_from_then wit' (FromThen expr1' expr2') }

tcArithSeq witness seq@(FromTo expr1 expr2) res_ty
  = do { (wrap, elt_mult, elt_ty, wit') <- arithSeqEltType witness res_ty
       ; expr1' <- tcScalingUsage elt_mult $ tcCheckPolyExpr expr1 elt_ty
       ; expr2' <- tcScalingUsage elt_mult $ tcCheckPolyExpr expr2 elt_ty
       ; enum_from_to <- newMethodFromName (ArithSeqOrigin seq)
                              enumFromToName [elt_ty]
       ; return $ mkHsWrap wrap $
         ArithSeq enum_from_to wit' (FromTo expr1' expr2') }

tcArithSeq witness seq@(FromThenTo expr1 expr2 expr3) res_ty
  = do { (wrap, elt_mult, elt_ty, wit') <- arithSeqEltType witness res_ty
        ; expr1' <- tcScalingUsage elt_mult $ tcCheckPolyExpr expr1 elt_ty
        ; expr2' <- tcScalingUsage elt_mult $ tcCheckPolyExpr expr2 elt_ty
        ; expr3' <- tcScalingUsage elt_mult $ tcCheckPolyExpr expr3 elt_ty
        ; eft <- newMethodFromName (ArithSeqOrigin seq)
                              enumFromThenToName [elt_ty]
        ; return $ mkHsWrap wrap $
          ArithSeq eft wit' (FromThenTo expr1' expr2' expr3') }

-----------------
arithSeqEltType :: Maybe (SyntaxExpr GhcRn) -> ExpRhoType
                -> TcM (HsWrapper, Mult, TcType, Maybe (SyntaxExpr GhcTc))
arithSeqEltType Nothing res_ty
  = do { res_ty <- expTypeToType res_ty
       ; (coi, elt_ty) <- matchExpectedListTy res_ty
       ; return (mkWpCastN coi, One, elt_ty, Nothing) }
arithSeqEltType (Just fl) res_ty
  = do { ((elt_mult, elt_ty), fl')
           <- tcSyntaxOp ListOrigin fl [SynList] res_ty $
              \ [elt_ty] [elt_mult] -> return (elt_mult, elt_ty)
       ; return (idHsWrapper, elt_mult, elt_ty, Just fl') }

{-
************************************************************************
*                                                                      *
                Applications
*                                                                      *
************************************************************************
-}

{- Note [Typechecking applications]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We typecheck application chains (f e1 @ty e2) specially:

* So we can report errors like "in the third arument of a call of f"

* So we can do Visible Type Application (VTA), for which we must not
  eagerly instantiate the function part of the application.

* So that we can do Quick Look impredicativity.

The idea is:

* Use collectHsArgs, which peels off
     HsApp, HsTypeApp, HsPrag, HsPar
  returning the function in the corner and the arguments

* Use tcInferAppHead to infer the type of the fuction,
    as an (uninstantiated) TcSigmaType
  There are special cases for
     HsVar, HsREcFld, and ExprWithTySig
  Otherwise, delegate back to tcExpr, which
    infers an (instantiated) TcRhoType

Some cases that /won't/ work:

1. Consider this (which uses visible type application):

    (let { f :: forall a. a -> a; f x = x } in f) @Int

   Since 'let' is not among the special cases for tcInferAppHead,
   we'll delegate back to tcExpr, which will instantiate f's type
   and the type application to @Int will fail.  Too bad!

-}

-- HsExprArg is a very local type, used only within this module.
-- It's really a zipper for an application chain
-- It's a GHC-specific type, so using TTG only where necessary
data HsExprArg id
  = HsEValArg  SrcSpan        -- Of the function
               (LHsExpr (GhcPass id))
  | HsETypeArg SrcSpan        -- Of the function
               (LHsWcType (NoGhcTc (GhcPass id)))
               !(XExprTypeArg id)
  | HsEPrag    SrcSpan
               (HsPragE (GhcPass id))
  | HsEPar     SrcSpan         -- Of the nested expr
  | HsEWrap    !(XArgWrap id)  -- Wrapper, after typechecking only

-- The outer location is the location of the application itself
type LHsExprArgIn  = HsExprArg 'Renamed
type LHsExprArgOut = HsExprArg 'Typechecked

instance OutputableBndrId id => Outputable (HsExprArg id) where
  ppr (HsEValArg _ tm)       = ppr tm
  ppr (HsEPrag _ p)          = text "HsPrag" <+> ppr p
  ppr (HsETypeArg _ hs_ty _) = char '@' <> ppr hs_ty
  ppr (HsEPar _)             = text "HsEPar"
  ppr (HsEWrap w)             = case ghcPass @id of
                                    GhcTc -> text "HsEWrap" <+> ppr w
                                    _     -> empty

type family XExprTypeArg id where
  XExprTypeArg 'Parsed      = NoExtField
  XExprTypeArg 'Renamed     = NoExtField
  XExprTypeArg 'Typechecked = Type

type family XArgWrap id where
  XArgWrap 'Parsed      = NoExtCon
  XArgWrap 'Renamed     = NoExtCon
  XArgWrap 'Typechecked = HsWrapper

addArgWrap :: HsWrapper -> [LHsExprArgOut] -> [LHsExprArgOut]
addArgWrap wrap args
 | isIdHsWrapper wrap = args
 | otherwise          = HsEWrap wrap : args

collectHsArgs :: HsExpr GhcRn -> (HsExpr GhcRn, [LHsExprArgIn])
collectHsArgs e = go e []
  where
    go (HsPar _     (L l fun))       args = go fun (HsEPar (locA l) : args)
    go (HsPragE _ p (L l fun))       args = go fun (HsEPrag (locA l) p : args)
    go (HsApp _     (L l fun) arg)   args = go fun (HsEValArg (locA l) arg : args)
    go (HsAppType _ (L l fun) hs_ty) args = go fun (HsETypeArg (locA l) hs_ty noExtField : args)
    go e                             args = (e,args)

applyHsArgs :: HsExpr GhcTc -> [LHsExprArgOut]-> HsExpr GhcTc
applyHsArgs fun args
  = go fun args
  where
    go fun [] = fun
    go fun (HsEWrap wrap : args)          = go (mkHsWrap wrap fun) args
    go fun (HsEValArg l arg : args)       = go (HsApp noAnn (L (noAnnSrcSpan l) fun) arg) args
    go fun (HsETypeArg l hs_ty ty : args) = go (HsAppType ty (L (noAnnSrcSpan l) fun) hs_ty) args
    go fun (HsEPar l : args)              = go (HsPar noAnn (L (noAnnSrcSpan l) fun)) args
    go fun (HsEPrag l p : args)           = go (HsPragE noExtField p (L (noAnnSrcSpan l) fun)) args

isHsValArg :: HsExprArg id -> Bool
isHsValArg (HsEValArg {}) = True
isHsValArg _              = False

isArgPar :: HsExprArg id -> Bool
isArgPar (HsEPar {}) = True
isArgPar _           = False

getFunLoc :: [HsExprArg 'Renamed] -> Maybe SrcSpan
getFunLoc []    = Nothing
getFunLoc (a:_) = Just $ case a of
                           HsEValArg l _    -> l
                           HsETypeArg l _ _ -> l
                           HsEPrag l _      -> l
                           HsEPar l         -> l

---------------------------
tcApp :: HsExpr GhcRn  -- either HsApp or HsAppType
       -> ExpRhoType -> TcM (HsExpr GhcTc)
-- See Note [Typechecking applications]
tcApp expr res_ty
  = do { (fun, args, app_res_ty) <- tcInferApp expr
       ; if isTagToEnum fun
         then tcTagToEnum expr fun args app_res_ty res_ty
              -- Done here because we have res_ty,
              -- whereas tcInferApp does not
         else

    -- The wildly common case
    do { let expr' = applyHsArgs fun args
       ; addFunResCtxt True fun app_res_ty res_ty $
         tcWrapResult expr expr' app_res_ty res_ty } }

---------------------------
tcInferApp :: HsExpr GhcRn
           -> TcM ( HsExpr GhcTc    -- Function
                  , [LHsExprArgOut]  -- Arguments
                  , TcSigmaType)     -- Inferred type: a sigma-type!
-- Also used by Module.tcRnExpr to implement GHCi :type
tcInferApp expr
  | -- Gruesome special case for ambiguous record selectors
    HsRecFld _ fld_lbl        <- fun
  , Ambiguous _ lbl           <- fld_lbl  -- Still ambiguous
  , HsEValArg _ (L _ arg) : _ <- filterOut isArgPar args -- A value arg is first
  , Just sig_ty               <- obviousSig arg  -- A type sig on the arg disambiguates
  = do { sig_tc_ty <- tcHsSigWcType ExprSigCtxt sig_ty
       ; sel_name  <- disambiguateSelector lbl sig_tc_ty
       ; (tc_fun, fun_ty) <- tcInferRecSelId (Unambiguous sel_name lbl)
       ; tcInferApp_finish fun tc_fun fun_ty args }

  | otherwise  -- The wildly common case
  = do { (tc_fun, fun_ty) <- set_fun_loc (tcInferAppHead fun)
       ; tcInferApp_finish fun tc_fun fun_ty args }
  where
    (fun, args) = collectHsArgs expr
    set_fun_loc thing_inside
      = case getFunLoc args of
          Nothing  -> thing_inside  -- Don't set the location twice
          Just loc -> setSrcSpan loc thing_inside

tcInferApp_finish
    :: HsExpr GhcRn                 -- Renamed function
    -> HsExpr GhcTc -> TcSigmaType  -- Function and its type
    -> [LHsExprArgIn]               -- Arguments
    -> TcM (HsExpr GhcTc, [LHsExprArgOut], TcSigmaType)
tcInferApp_finish rn_fun tc_fun fun_sigma rn_args
  = do { (tc_args, actual_res_ty) <- tcArgs rn_fun fun_sigma rn_args
       ; return (tc_fun, tc_args, actual_res_ty) }

mk_op_msg :: LHsExpr GhcRn -> SDoc
mk_op_msg op = text "The operator" <+> quotes (ppr op) <+> text "takes"

----------------
tcInferAppHead :: HsExpr GhcRn -> TcM (HsExpr GhcTc, TcSigmaType)
-- Infer type of the head of an application, returning a /SigmaType/
--   i.e. the 'f' in (f e1 ... en)
-- We get back a SigmaType because we have special cases for
--   * A bare identifier (just look it up)
--     This case also covers a record selectro HsRecFld
--   * An expression with a type signature (e :: ty)
--
-- Note that [] and (,,) are both HsVar:
--   see Note [Empty lists] and [ExplicitTuple] in GHC.Hs.Expr
--
-- NB: 'e' cannot be HsApp, HsTyApp, HsPrag, HsPar, because those
--     cases are dealt with by collectHsArgs.
--
-- See Note [Typechecking applications]
tcInferAppHead e
  = case e of
      HsVar _ (L _ nm)        -> tcInferId nm
      HsRecFld _ f            -> tcInferRecSelId f
      ExprWithTySig _ e hs_ty -> add_ctxt $ tcExprWithSig e hs_ty
      _                       -> add_ctxt $ tcInfer (tcExpr e)
  where
    add_ctxt thing = addErrCtxt (exprCtxt e) thing

----------------
-- | Type-check the arguments to a function, possibly including visible type
-- applications
tcArgs :: HsExpr GhcRn   -- ^ The function itself (for err msgs only)
       -> TcSigmaType    -- ^ the (uninstantiated) type of the function
       -> [LHsExprArgIn] -- ^ the args
       -> TcM ([LHsExprArgOut], TcSigmaType)
          -- ^ (a wrapper for the function, the tc'd args, result type)
tcArgs fun orig_fun_ty orig_args
  = go 1 [] orig_fun_ty orig_args
  where
    fun_orig = exprCtOrigin fun
    herald = sep [ text "The function" <+> quotes (ppr fun)
                 , text "is applied to"]

    -- Count value args only when complaining about a function
    -- applied to too many value args
    -- See Note [Herald for matchExpectedFunTys] in GHC.Tc.Utils.Unify.
    n_val_args = count isHsValArg orig_args

    fun_is_out_of_scope  -- See Note [VTA for out-of-scope functions]
      = case fun of
          HsUnboundVar {} -> True
          _               -> False

    go :: Int           -- Which argment number this is (incl type args)
       -> [Scaled TcSigmaType] -- Value args to which applied so far
       -> TcSigmaType
       -> [LHsExprArgIn] -> TcM ([LHsExprArgOut], TcSigmaType)
    go _ _ fun_ty [] = traceTc "tcArgs:ret" (ppr fun_ty) >> return ([], fun_ty)

    go n so_far fun_ty (HsEPar sp : args)
      = do { (args', res_ty) <- go n so_far fun_ty args
           ; return (HsEPar sp : args', res_ty) }

    go n so_far fun_ty (HsEPrag sp prag : args)
      = do { (args', res_ty) <- go n so_far fun_ty args
           ; return (HsEPrag sp (tcExprPrag prag) : args', res_ty) }

    go n so_far fun_ty (HsETypeArg loc hs_ty_arg _ : args)
      | fun_is_out_of_scope   -- See Note [VTA for out-of-scope functions]
      = go (n+1) so_far fun_ty args

      | otherwise
      = do { (wrap1, upsilon_ty) <- topInstantiateInferred fun_orig fun_ty
               -- wrap1 :: fun_ty "->" upsilon_ty
           ; case tcSplitForAllTy_maybe upsilon_ty of
               Just (tvb, inner_ty)
                 | binderArgFlag tvb == Specified ->
                   -- It really can't be Inferred, because we've justn
                   -- instantiated those. But, oddly, it might just be Required.
                   -- See Note [Required quantifiers in the type of a term]
                 do { let tv   = binderVar tvb
                          kind = tyVarKind tv
                    ; ty_arg <- tcHsTypeApp hs_ty_arg kind

                    ; inner_ty <- zonkTcType inner_ty
                          -- See Note [Visible type application zonk]
                    ; let in_scope  = mkInScopeSet (tyCoVarsOfTypes [upsilon_ty, ty_arg])
                          insted_ty = substTyWithInScope in_scope [tv] [ty_arg] inner_ty
                                      -- NB: tv and ty_arg have the same kind, so this
                                      --     substitution is kind-respecting
                    ; traceTc "VTA" (vcat [ppr tv, debugPprType kind
                                          , debugPprType ty_arg
                                          , debugPprType (tcTypeKind ty_arg)
                                          , debugPprType inner_ty
                                          , debugPprType insted_ty ])

                    ; (args', res_ty) <- go (n+1) so_far insted_ty args
                    ; return ( addArgWrap wrap1 $ HsETypeArg loc hs_ty_arg ty_arg : args'
                             , res_ty ) }
               _ -> ty_app_err upsilon_ty hs_ty_arg }

    go n so_far fun_ty (HsEValArg loc arg : args)
      = do { (wrap, arg_ty, res_ty)
               <- matchActualFunTySigma herald fun_orig (Just fun)
                                        (n_val_args, so_far) fun_ty
           ; arg' <- tcArg fun arg arg_ty n
           ; (args', inner_res_ty) <- go (n+1) (arg_ty:so_far) res_ty args
           ; return ( addArgWrap wrap $ HsEValArg loc arg' : args'
                    , inner_res_ty ) }

    ty_app_err ty arg
      = do { (_, ty) <- zonkTidyTcType emptyTidyEnv ty
           ; failWith $
               text "Cannot apply expression of type" <+> quotes (ppr ty) $$
               text "to a visible type argument" <+> quotes (ppr arg) }

{- Note [Required quantifiers in the type of a term]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider (#15859)

  data A k :: k -> Type      -- A      :: forall k -> k -> Type
  type KindOf (a :: k) = k   -- KindOf :: forall k. k -> Type
  a = (undefind :: KindOf A) @Int

With ImpredicativeTypes (thin ice, I know), we instantiate
KindOf at type (forall k -> k -> Type), so
  KindOf A = forall k -> k -> Type
whose first argument is Required

We want to reject this type application to Int, but in earlier
GHCs we had an ASSERT that Required could not occur here.

The ice is thin; c.f. Note [No Required TyCoBinder in terms]
in GHC.Core.TyCo.Rep.

Note [VTA for out-of-scope functions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose 'wurble' is not in scope, and we have
   (wurble @Int @Bool True 'x')

Then the renamer will make (HsUnboundVar "wurble) for 'wurble',
and the typechecker will typecheck it with tcUnboundId, giving it
a type 'alpha', and emitting a deferred Hole, to be reported later.

But then comes the visible type application. If we do nothing, we'll
generate an immediate failure (in tc_app_err), saying that a function
of type 'alpha' can't be applied to Bool.  That's insane!  And indeed
users complain bitterly (#13834, #17150.)

The right error is the Hole, which has /already/ been emitted by
tcUnboundId.  It later reports 'wurble' as out of scope, and tries to
give its type.

Fortunately in tcArgs we still have access to the function, so we can
check if it is a HsUnboundVar.  We use this info to simply skip over
any visible type arguments.  We've already inferred the type of the
function, so we'll /already/ have emitted a Hole;
failing preserves that constraint.

We do /not/ want to fail altogether in this case (via failM) becuase
that may abandon an entire instance decl, which (in the presence of
-fdefer-type-errors) leads to leading to #17792.

Downside; the typechecked term has lost its visible type arguments; we
don't even kind-check them.  But let's jump that bridge if we come to
it.  Meanwhile, let's not crash!

Note [Visible type application zonk]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* Substitutions should be kind-preserving, so we need kind(tv) = kind(ty_arg).

* tcHsTypeApp only guarantees that
    - ty_arg is zonked
    - kind(zonk(tv)) = kind(ty_arg)
  (checkExpectedKind zonks as it goes).

So we must zonk inner_ty as well, to guarantee consistency between zonk(tv)
and inner_ty.  Otherwise we can build an ill-kinded type.  An example was
#14158, where we had:
   id :: forall k. forall (cat :: k -> k -> *). forall (a :: k). cat a a
and we had the visible type application
  id @(->)

* We instantiated k := kappa, yielding
    forall (cat :: kappa -> kappa -> *). forall (a :: kappa). cat a a
* Then we called tcHsTypeApp (->) with expected kind (kappa -> kappa -> *).
* That instantiated (->) as ((->) q1 q1), and unified kappa := q1,
  Here q1 :: RuntimeRep
* Now we substitute
     cat  :->  (->) q1 q1 :: TYPE q1 -> TYPE q1 -> *
  but we must first zonk the inner_ty to get
      forall (a :: TYPE q1). cat a a
  so that the result of substitution is well-kinded
  Failing to do so led to #14158.
-}

----------------
tcArg :: HsExpr GhcRn                   -- The function (for error messages)
      -> LHsExpr GhcRn                   -- Actual arguments
      -> Scaled TcSigmaType              -- expected arg type
      -> Int                             -- # of argument
      -> TcM (LHsExpr GhcTc)           -- Resulting argument
tcArg fun arg (Scaled mult ty) arg_no
   = addErrCtxt (funAppCtxt fun arg arg_no) $
     do { traceTc "tcArg" $
          vcat [ ppr arg_no <+> text "of" <+> ppr fun
               , text "arg type:" <+> ppr ty
               , text "arg:" <+> ppr arg ]
        ; tcScalingUsage mult $ tcCheckPolyExprNC arg ty }

----------------
tcTupArgs :: [LHsTupArg GhcRn] -> [TcSigmaType] -> TcM [LHsTupArg GhcTc]
tcTupArgs args tys
  = ASSERT( equalLength args tys ) mapM go (args `zip` tys)
  where
    go (L l (Missing {}),   arg_ty) = do { mult <- newFlexiTyVarTy multiplicityTy
                                         ; return (L l (Missing (Scaled mult arg_ty))) }
    go (L l (Present x expr), arg_ty) = do { expr' <- tcCheckPolyExpr expr arg_ty
                                           ; return (L l (Present x expr')) }

---------------------------
-- See TcType.SyntaxOpType also for commentary
tcSyntaxOp :: CtOrigin
           -> SyntaxExprRn
           -> [SyntaxOpType]           -- ^ shape of syntax operator arguments
           -> ExpRhoType               -- ^ overall result type
           -> ([TcSigmaType] -> [Mult] -> TcM a) -- ^ Type check any arguments,
                                                 -- takes a type per hole and a
                                                 -- multiplicity per arrow in
                                                 -- the shape.
           -> TcM (a, SyntaxExprTc)
-- ^ Typecheck a syntax operator
-- The operator is a variable or a lambda at this stage (i.e. renamer
-- output)
tcSyntaxOp orig expr arg_tys res_ty
  = tcSyntaxOpGen orig expr arg_tys (SynType res_ty)

-- | Slightly more general version of 'tcSyntaxOp' that allows the caller
-- to specify the shape of the result of the syntax operator
tcSyntaxOpGen :: CtOrigin
              -> SyntaxExprRn
              -> [SyntaxOpType]
              -> SyntaxOpType
              -> ([TcSigmaType] -> [Mult] -> TcM a)
              -> TcM (a, SyntaxExprTc)
tcSyntaxOpGen orig (SyntaxExprRn op) arg_tys res_ty thing_inside
  = do { (expr, sigma) <- tcInferAppHead op
       ; traceTc "tcSyntaxOpGen" (ppr op $$ ppr expr $$ ppr sigma)
       ; (result, expr_wrap, arg_wraps, res_wrap)
           <- tcSynArgA orig sigma arg_tys res_ty $
              thing_inside
       ; traceTc "tcSyntaxOpGen" (ppr op $$ ppr expr $$ ppr sigma )
       ; return (result, SyntaxExprTc { syn_expr = mkHsWrap expr_wrap expr
                                      , syn_arg_wraps = arg_wraps
                                      , syn_res_wrap  = res_wrap }) }
tcSyntaxOpGen _ NoSyntaxExprRn _ _ _ = panic "tcSyntaxOpGen"

{-
Note [tcSynArg]
~~~~~~~~~~~~~~~
Because of the rich structure of SyntaxOpType, we must do the
contra-/covariant thing when working down arrows, to get the
instantiation vs. skolemisation decisions correct (and, more
obviously, the orientation of the HsWrappers). We thus have
two tcSynArgs.
-}

-- works on "expected" types, skolemising where necessary
-- See Note [tcSynArg]
tcSynArgE :: CtOrigin
          -> TcSigmaType
          -> SyntaxOpType                -- ^ shape it is expected to have
          -> ([TcSigmaType] -> [Mult] -> TcM a) -- ^ check the arguments
          -> TcM (a, HsWrapper)
           -- ^ returns a wrapper :: (type of right shape) "->" (type passed in)
tcSynArgE orig sigma_ty syn_ty thing_inside
  = do { (skol_wrap, (result, ty_wrapper))
           <- tcSkolemise GenSigCtxt sigma_ty $ \ rho_ty ->
              go rho_ty syn_ty
       ; return (result, skol_wrap <.> ty_wrapper) }
    where
    go rho_ty SynAny
      = do { result <- thing_inside [rho_ty] []
           ; return (result, idHsWrapper) }

    go rho_ty SynRho   -- same as SynAny, because we skolemise eagerly
      = do { result <- thing_inside [rho_ty] []
           ; return (result, idHsWrapper) }

    go rho_ty SynList
      = do { (list_co, elt_ty) <- matchExpectedListTy rho_ty
           ; result <- thing_inside [elt_ty] []
           ; return (result, mkWpCastN list_co) }

    go rho_ty (SynFun arg_shape res_shape)
      = do { ( match_wrapper                         -- :: (arg_ty -> res_ty) "->" rho_ty
             , ( ( (result, arg_ty, res_ty, op_mult)
                 , res_wrapper )                     -- :: res_ty_out "->" res_ty
               , arg_wrapper1, [], arg_wrapper2 ) )  -- :: arg_ty "->" arg_ty_out
               <- matchExpectedFunTys herald GenSigCtxt 1 (mkCheckExpType rho_ty) $
                  \ [arg_ty] res_ty ->
                  do { arg_tc_ty <- expTypeToType (scaledThing arg_ty)
                     ; res_tc_ty <- expTypeToType res_ty

                         -- another nested arrow is too much for now,
                         -- but I bet we'll never need this
                     ; MASSERT2( case arg_shape of
                                   SynFun {} -> False;
                                   _         -> True
                               , text "Too many nested arrows in SyntaxOpType" $$
                                 pprCtOrigin orig )

                     ; let arg_mult = scaledMult arg_ty
                     ; tcSynArgA orig arg_tc_ty [] arg_shape $
                       \ arg_results arg_res_mults ->
                       tcSynArgE orig res_tc_ty res_shape $
                       \ res_results res_res_mults ->
                       do { result <- thing_inside (arg_results ++ res_results) ([arg_mult] ++ arg_res_mults ++ res_res_mults)
                          ; return (result, arg_tc_ty, res_tc_ty, arg_mult) }}

           ; return ( result
                    , match_wrapper <.>
                      mkWpFun (arg_wrapper2 <.> arg_wrapper1) res_wrapper
                              (Scaled op_mult arg_ty) res_ty doc ) }
      where
        herald = text "This rebindable syntax expects a function with"
        doc = text "When checking a rebindable syntax operator arising from" <+> ppr orig

    go rho_ty (SynType the_ty)
      = do { wrap   <- tcSubTypePat orig GenSigCtxt the_ty rho_ty
           ; result <- thing_inside [] []
           ; return (result, wrap) }

-- works on "actual" types, instantiating where necessary
-- See Note [tcSynArg]
tcSynArgA :: CtOrigin
          -> TcSigmaType
          -> [SyntaxOpType]              -- ^ argument shapes
          -> SyntaxOpType                -- ^ result shape
          -> ([TcSigmaType] -> [Mult] -> TcM a) -- ^ check the arguments
          -> TcM (a, HsWrapper, [HsWrapper], HsWrapper)
            -- ^ returns a wrapper to be applied to the original function,
            -- wrappers to be applied to arguments
            -- and a wrapper to be applied to the overall expression
tcSynArgA orig sigma_ty arg_shapes res_shape thing_inside
  = do { (match_wrapper, arg_tys, res_ty)
           <- matchActualFunTysRho herald orig Nothing
                                   (length arg_shapes) sigma_ty
              -- match_wrapper :: sigma_ty "->" (arg_tys -> res_ty)
       ; ((result, res_wrapper), arg_wrappers)
           <- tc_syn_args_e (map scaledThing arg_tys) arg_shapes $ \ arg_results arg_res_mults ->
              tc_syn_arg    res_ty  res_shape  $ \ res_results ->
              thing_inside (arg_results ++ res_results) (map scaledMult arg_tys ++ arg_res_mults)
       ; return (result, match_wrapper, arg_wrappers, res_wrapper) }
  where
    herald = text "This rebindable syntax expects a function with"

    tc_syn_args_e :: [TcSigmaType] -> [SyntaxOpType]
                  -> ([TcSigmaType] -> [Mult] -> TcM a)
                  -> TcM (a, [HsWrapper])
                    -- the wrappers are for arguments
    tc_syn_args_e (arg_ty : arg_tys) (arg_shape : arg_shapes) thing_inside
      = do { ((result, arg_wraps), arg_wrap)
               <- tcSynArgE     orig arg_ty  arg_shape  $ \ arg1_results arg1_mults ->
                  tc_syn_args_e      arg_tys arg_shapes $ \ args_results args_mults ->
                  thing_inside (arg1_results ++ args_results) (arg1_mults ++ args_mults)
           ; return (result, arg_wrap : arg_wraps) }
    tc_syn_args_e _ _ thing_inside = (, []) <$> thing_inside [] []

    tc_syn_arg :: TcSigmaType -> SyntaxOpType
               -> ([TcSigmaType] -> TcM a)
               -> TcM (a, HsWrapper)
                  -- the wrapper applies to the overall result
    tc_syn_arg res_ty SynAny thing_inside
      = do { result <- thing_inside [res_ty]
           ; return (result, idHsWrapper) }
    tc_syn_arg res_ty SynRho thing_inside
      = do { (inst_wrap, rho_ty) <- topInstantiate orig res_ty
               -- inst_wrap :: res_ty "->" rho_ty
           ; result <- thing_inside [rho_ty]
           ; return (result, inst_wrap) }
    tc_syn_arg res_ty SynList thing_inside
      = do { (inst_wrap, rho_ty) <- topInstantiate orig res_ty
               -- inst_wrap :: res_ty "->" rho_ty
           ; (list_co, elt_ty)   <- matchExpectedListTy rho_ty
               -- list_co :: [elt_ty] ~N rho_ty
           ; result <- thing_inside [elt_ty]
           ; return (result, mkWpCastN (mkTcSymCo list_co) <.> inst_wrap) }
    tc_syn_arg _ (SynFun {}) _
      = pprPanic "tcSynArgA hits a SynFun" (ppr orig)
    tc_syn_arg res_ty (SynType the_ty) thing_inside
      = do { wrap   <- tcSubType orig GenSigCtxt res_ty the_ty
           ; result <- thing_inside []
           ; return (result, wrap) }

{-
Note [Push result type in]
~~~~~~~~~~~~~~~~~~~~~~~~~~
Unify with expected result before type-checking the args so that the
info from res_ty percolates to args.  This is when we might detect a
too-few args situation.  (One can think of cases when the opposite
order would give a better error message.)
experimenting with putting this first.

Here's an example where it actually makes a real difference

   class C t a b | t a -> b
   instance C Char a Bool

   data P t a = forall b. (C t a b) => MkP b
   data Q t   = MkQ (forall a. P t a)

   f1, f2 :: Q Char;
   f1 = MkQ (MkP True)
   f2 = MkQ (MkP True :: forall a. P Char a)

With the change, f1 will type-check, because the 'Char' info from
the signature is propagated into MkQ's argument. With the check
in the other order, the extra signature in f2 is reqd.

************************************************************************
*                                                                      *
                Expressions with a type signature
                        expr :: type
*                                                                      *
********************************************************************* -}

tcExprSig :: LHsExpr GhcRn -> TcIdSigInfo -> TcM (LHsExpr GhcTc, TcType)
tcExprSig expr (CompleteSig { sig_bndr = poly_id, sig_loc = loc })
  = setSrcSpan loc $   -- Sets the location for the implication constraint
    do { let poly_ty = idType poly_id
       ; (wrap, expr') <- tcSkolemiseScoped ExprSigCtxt poly_ty $ \rho_ty ->
                          tcCheckMonoExprNC expr rho_ty
       ; return (mkLHsWrap wrap expr', poly_ty) }

tcExprSig expr sig@(PartialSig { psig_name = name, sig_loc = loc })
  = setSrcSpan loc $   -- Sets the location for the implication constraint
    do { (tclvl, wanted, (expr', sig_inst))
             <- pushLevelAndCaptureConstraints  $
                do { sig_inst <- tcInstSig sig
                   ; expr' <- tcExtendNameTyVarEnv (mapSnd binderVar $ sig_inst_skols sig_inst) $
                              tcExtendNameTyVarEnv (sig_inst_wcs   sig_inst) $
                              tcCheckPolyExprNC expr (sig_inst_tau sig_inst)
                   ; return (expr', sig_inst) }
       -- See Note [Partial expression signatures]
       ; let tau = sig_inst_tau sig_inst
             infer_mode | null (sig_inst_theta sig_inst)
                        , isNothing (sig_inst_wcx sig_inst)
                        = ApplyMR
                        | otherwise
                        = NoRestrictions
       ; (qtvs, givens, ev_binds, residual, _)
                 <- simplifyInfer tclvl infer_mode [sig_inst] [(name, tau)] wanted
       ; emitConstraints residual

       ; tau <- zonkTcType tau
       ; let inferred_theta = map evVarPred givens
             tau_tvs        = tyCoVarsOfType tau
       ; (binders, my_theta) <- chooseInferredQuantifiers inferred_theta
                                   tau_tvs qtvs (Just sig_inst)
       ; let inferred_sigma = mkInfSigmaTy qtvs inferred_theta tau
             my_sigma       = mkInvisForAllTys binders (mkPhiTy  my_theta tau)
       ; wrap <- if inferred_sigma `eqType` my_sigma -- NB: eqType ignores vis.
                 then return idHsWrapper  -- Fast path; also avoids complaint when we infer
                                          -- an ambiguous type and have AllowAmbiguousType
                                          -- e..g infer  x :: forall a. F a -> Int
                 else tcSubTypeSigma ExprSigCtxt inferred_sigma my_sigma

       ; traceTc "tcExpSig" (ppr qtvs $$ ppr givens $$ ppr inferred_sigma $$ ppr my_sigma)
       ; let poly_wrap = wrap
                         <.> mkWpTyLams qtvs
                         <.> mkWpLams givens
                         <.> mkWpLet  ev_binds
       ; return (mkLHsWrap poly_wrap expr', my_sigma) }


{- Note [Partial expression signatures]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Partial type signatures on expressions are easy to get wrong.  But
here is a guiding principile
    e :: ty
should behave like
    let x :: ty
        x = e
    in x

So for partial signatures we apply the MR if no context is given.  So
   e :: IO _          apply the MR
   e :: _ => IO _     do not apply the MR
just like in GHC.Tc.Gen.Bind.decideGeneralisationPlan

This makes a difference (#11670):
   peek :: Ptr a -> IO CLong
   peek ptr = peekElemOff undefined 0 :: _
from (peekElemOff undefined 0) we get
          type: IO w
   constraints: Storable w

We must NOT try to generalise over 'w' because the signature specifies
no constraints so we'll complain about not being able to solve
Storable w.  Instead, don't generalise; then _ gets instantiated to
CLong, as it should.
-}

{- *********************************************************************
*                                                                      *
                 tcInferId
*                                                                      *
********************************************************************* -}

tcCheckId :: Name -> ExpRhoType -> TcM (HsExpr GhcTc)
tcCheckId name res_ty
  | name `hasKey` tagToEnumKey
  = failWithTc (text "tagToEnum# must appear applied to one argument")
    -- tcApp catches the case (tagToEnum# arg)

  | otherwise
  = do { (expr, actual_res_ty) <- tcInferId name
       ; traceTc "tcCheckId" (vcat [ppr name, ppr actual_res_ty, ppr res_ty])
       ; addFunResCtxt False expr actual_res_ty res_ty $
         tcWrapResultO (OccurrenceOf name) (HsVar noExtField (noLocA name)) expr
                                           actual_res_ty res_ty }

tcCheckRecSelId :: HsExpr GhcRn -> AmbiguousFieldOcc GhcRn -> ExpRhoType -> TcM (HsExpr GhcTc)
tcCheckRecSelId rn_expr f@(Unambiguous {}) res_ty
  = do { (expr, actual_res_ty) <- tcInferRecSelId f
       ; tcWrapResult rn_expr expr actual_res_ty res_ty }
tcCheckRecSelId rn_expr (Ambiguous _ lbl) res_ty
  = case tcSplitFunTy_maybe =<< checkingExpType_maybe res_ty of
      Nothing       -> ambiguousSelector lbl
      Just (arg, _) -> do { sel_name <- disambiguateSelector lbl (scaledThing arg)
                          ; tcCheckRecSelId rn_expr (Unambiguous sel_name lbl)
                                                    res_ty }

------------------------
tcInferRecSelId :: AmbiguousFieldOcc GhcRn -> TcM (HsExpr GhcTc, TcRhoType)
tcInferRecSelId (Unambiguous sel (L _ lbl))
  = do { (expr', ty) <- tc_infer_id lbl sel
       ; return (expr', ty) }
tcInferRecSelId (Ambiguous _ lbl)
  = ambiguousSelector lbl

------------------------
tcInferId :: Name -> TcM (HsExpr GhcTc, TcSigmaType)
-- Look up an occurrence of an Id
-- Do not instantiate its type
tcInferId id_name
  | id_name `hasKey` assertIdKey
  = do { dflags <- getDynFlags
       ; if gopt Opt_IgnoreAsserts dflags
         then tc_infer_id (nameRdrName id_name) id_name
         else tc_infer_assert id_name }

  | otherwise
  = do { (expr, ty) <- tc_infer_id (nameRdrName id_name) id_name
       ; traceTc "tcInferId" (ppr id_name <+> dcolon <+> ppr ty)
       ; return (expr, ty) }

tc_infer_assert :: Name -> TcM (HsExpr GhcTc, TcSigmaType)
-- Deal with an occurrence of 'assert'
-- See Note [Adding the implicit parameter to 'assert']
tc_infer_assert assert_name
  = do { assert_error_id <- tcLookupId assertErrorName
       ; (wrap, id_rho) <- topInstantiate (OccurrenceOf assert_name)
                                          (idType assert_error_id)
       ; return (mkHsWrap wrap (HsVar noExtField (noLocA assert_error_id)), id_rho)
       }

tc_infer_id :: RdrName -> Name -> TcM (HsExpr GhcTc, TcSigmaType)
tc_infer_id lbl id_name
 = do { thing <- tcLookup id_name
      ; case thing of
             ATcId { tct_id = id }
               -> do { check_naughty id        -- Note [Local record selectors]
                     ; checkThLocalId id
                     ; tcEmitBindingUsage $ unitUE id_name One
                     ; return_id id }

             AGlobal (AnId id)
               -> do { check_naughty id
                     ; return_id id }
                    -- A global cannot possibly be ill-staged
                    -- nor does it need the 'lifting' treatment
                    -- hence no checkTh stuff here

             AGlobal (AConLike cl) -> case cl of
                 RealDataCon con -> return_data_con con
                 PatSynCon ps    -> tcPatSynBuilderOcc ps

             _ -> failWithTc $
                  ppr thing <+> text "used where a value identifier was expected" }
  where
    return_id id = return (HsVar noExtField (noLocA id), idType id)

    return_data_con con
      = do { let tvs = dataConUserTyVarBinders con
                 theta = dataConOtherTheta con
                 args = dataConOrigArgTys con
                 res = dataConOrigResTy con

           -- See Note [Linear fields generalization]
           ; mul_vars <- newFlexiTyVarTys (length args) multiplicityTy
           ; let scaleArgs args' = zipWithEqual "return_data_con" combine mul_vars args'
                 combine var (Scaled One ty) = Scaled var ty
                 combine _   scaled_ty       = scaled_ty
                   -- The combine function implements the fact that, as
                   -- described in Note [Linear fields generalization], if a
                   -- field is not linear (last line) it isn't made polymorphic.

                 etaWrapper arg_tys = foldr (\scaled_ty wr -> WpFun WpHole wr scaled_ty empty) WpHole arg_tys

           -- See Note [Instantiating stupid theta]
           ; let shouldInstantiate = (not (null (dataConStupidTheta con)) ||
                                      isKindLevPoly (tyConResKind (dataConTyCon con)))
           ; case shouldInstantiate of
               True -> do { (subst, tvs') <- newMetaTyVars (binderVars tvs)
                           ; let tys'   = mkTyVarTys tvs'
                                 theta' = substTheta subst theta
                                 args'  = substScaledTys subst args
                                 res'   = substTy subst res
                           ; wrap <- instCall (OccurrenceOf id_name) tys' theta'
                           ; let scaled_arg_tys = scaleArgs args'
                                 eta_wrap = etaWrapper scaled_arg_tys
                           ; addDataConStupidTheta con tys'
                           ; return ( mkHsWrap (eta_wrap <.> wrap)
                                               (HsConLikeOut noExtField (RealDataCon con))
                                    , mkVisFunTys scaled_arg_tys res')
                           }
               False -> let scaled_arg_tys = scaleArgs args
                            wrap1 = mkWpTyApps (mkTyVarTys $ binderVars tvs)
                            eta_wrap = etaWrapper (map unrestricted theta ++ scaled_arg_tys)
                            wrap2 = mkWpTyLams $ binderVars tvs
                        in return ( mkHsWrap (wrap2 <.> eta_wrap <.> wrap1)
                                             (HsConLikeOut noExtField (RealDataCon con))
                                  , mkInvisForAllTys tvs $ mkInvisFunTysMany theta $ mkVisFunTys scaled_arg_tys res)
           }

    check_naughty id
      | isNaughtyRecordSelector id = failWithTc (naughtyRecordSel lbl)
      | otherwise                  = return ()


tcUnboundId :: HsExpr GhcRn -> OccName -> ExpRhoType -> TcM (HsExpr GhcTc)
-- Typecheck an occurrence of an unbound Id
--
-- Some of these started life as a true expression hole "_".
-- Others might simply be variables that accidentally have no binding site
--
-- We turn all of them into HsVar, since HsUnboundVar can't contain an
-- Id; and indeed the evidence for the ExprHole does bind it, so it's
-- not unbound any more!
tcUnboundId rn_expr occ res_ty
 = do { ty <- newOpenFlexiTyVarTy  -- Allow Int# etc (#12531)
      ; name <- newSysName occ
      ; let ev = mkLocalId name Many ty
      ; emitNewExprHole occ ev ty
      ; tcWrapResultO (UnboundOccurrenceOf occ) rn_expr
          (HsVar noExtField (noLocA ev)) ty res_ty }


{-
Note [Adding the implicit parameter to 'assert']
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The typechecker transforms (assert e1 e2) to (assertError e1 e2).
This isn't really the Right Thing because there's no way to "undo"
if you want to see the original source code in the typechecker
output.  We'll have fix this in due course, when we care more about
being able to reconstruct the exact original program.

Note [tagToEnum#]
~~~~~~~~~~~~~~~~~
Nasty check to ensure that tagToEnum# is applied to a type that is an
enumeration TyCon.  Unification may refine the type later, but this
check won't see that, alas.  It's crude, because it relies on our
knowing *now* that the type is ok, which in turn relies on the
eager-unification part of the type checker pushing enough information
here.  In theory the Right Thing to do is to have a new form of
constraint but I definitely cannot face that!  And it works ok as-is.

Here's are two cases that should fail
        f :: forall a. a
        f = tagToEnum# 0        -- Can't do tagToEnum# at a type variable

        g :: Int
        g = tagToEnum# 0        -- Int is not an enumeration

When data type families are involved it's a bit more complicated.
     data family F a
     data instance F [Int] = A | B | C
Then we want to generate something like
     tagToEnum# R:FListInt 3# |> co :: R:FListInt ~ F [Int]
Usually that coercion is hidden inside the wrappers for
constructors of F [Int] but here we have to do it explicitly.

It's all grotesquely complicated.

Note [Instantiating stupid theta]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Normally, when we infer the type of an Id, we don't instantiate,
because we wish to allow for visible type application later on.
But if a datacon has a stupid theta, we're a bit stuck. We need
to emit the stupid theta constraints with instantiated types. It's
difficult to defer this to the lazy instantiation, because a stupid
theta has no spot to put it in a type. So we just instantiate eagerly
in this case. Thus, users cannot use visible type application with
a data constructor sporting a stupid theta. I won't feel so bad for
the users that complain.

Note [Linear fields generalization]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As per Note [Polymorphisation of linear fields], linear field of data
constructors get a polymorphic type when the data constructor is used as a term.

    Just :: forall {p} a. a #p-> Maybe a

This rule is known only to the typechecker: Just keeps its linear type in Core.

In order to desugar this generalised typing rule, we simply eta-expand:

    \a (x # p :: a) -> Just @a x

has the appropriate type. We insert these eta-expansion with WpFun wrappers.

A small hitch: if the constructor is levity-polymorphic (unboxed tuples, sums,
certain newtypes with -XUnliftedNewtypes) then this strategy produces

    \r1 r2 a b (x # p :: a) (y # q :: b) -> (# a, b #)

Which has type

    forall r1 r2 a b. a #p-> b #q-> (# a, b #)

Which violates the levity-polymorphism restriction see Note [Levity polymorphism
checking] in DsMonad.

So we really must instantiate r1 and r2 rather than quantify over them.  For
simplicity, we just instantiate the entire type, as described in Note
[Instantiating stupid theta]. It breaks visible type application with unboxed
tuples, sums and levity-polymorphic newtypes, but this doesn't appear to be used
anywhere.

A better plan: let's force all representation variable to be *inferred*, so that
they are not subject to visible type applications. Then we can instantiate
inferred argument eagerly.
-}

isTagToEnum :: HsExpr GhcTc -> Bool
isTagToEnum (HsVar _ (L _ fun_id)) = fun_id `hasKey` tagToEnumKey
isTagToEnum _ = False

tcTagToEnum :: HsExpr GhcRn -> HsExpr GhcTc -> [LHsExprArgOut]
            -> TcSigmaType -> ExpRhoType
            -> TcM (HsExpr GhcTc)
-- tagToEnum# :: forall a. Int# -> a
-- See Note [tagToEnum#]   Urgh!
tcTagToEnum expr fun args app_res_ty res_ty
  = do { res_ty <- readExpType res_ty
       ; ty'    <- zonkTcType res_ty

       -- Check that the type is algebraic
       ; case tcSplitTyConApp_maybe ty' of {
           Nothing -> do { addErrTc (mk_error ty' doc1)
                         ; vanilla_result } ;
           Just (tc, tc_args) ->

    do { -- Look through any type family
       ; fam_envs <- tcGetFamInstEnvs
       ; case tcLookupDataFamInst_maybe fam_envs tc tc_args of {
           Nothing -> do { check_enumeration ty' tc
                         ; vanilla_result } ;
           Just (rep_tc, rep_args, coi) ->

    do { -- coi :: tc tc_args ~R rep_tc rep_args
         check_enumeration ty' rep_tc
       ; let val_arg = dropWhile (not . isHsValArg) args
             rep_ty  = mkTyConApp rep_tc rep_args
             fun'    = mkHsWrap (WpTyApp rep_ty) fun
             expr'   = applyHsArgs fun' val_arg
             df_wrap = mkWpCastR (mkTcSymCo coi)
       ; return (mkHsWrap df_wrap expr') }}}}}

  where
    vanilla_result
      = do { let expr' = applyHsArgs fun args
           ; tcWrapResult expr expr' app_res_ty res_ty }

    check_enumeration ty' tc
      | isEnumerationTyCon tc = return ()
      | otherwise             = addErrTc (mk_error ty' doc2)

    doc1 = vcat [ text "Specify the type by giving a type signature"
                , text "e.g. (tagToEnum# x) :: Bool" ]
    doc2 = text "Result type must be an enumeration type"

    mk_error :: TcType -> SDoc -> SDoc
    mk_error ty what
      = hang (text "Bad call to tagToEnum#"
               <+> text "at type" <+> ppr ty)
           2 what

{-
************************************************************************
*                                                                      *
                 Template Haskell checks
*                                                                      *
************************************************************************
-}

checkThLocalId :: Id -> TcM ()
-- The renamer has already done checkWellStaged,
--   in 'GHC.Rename.Splice.checkThLocalName', so don't repeat that here.
-- Here we just add constraints fro cross-stage lifting
checkThLocalId id
  = do  { mb_local_use <- getStageAndBindLevel (idName id)
        ; case mb_local_use of
             Just (top_lvl, bind_lvl, use_stage)
                | thLevel use_stage > bind_lvl
                -> checkCrossStageLifting top_lvl id use_stage
             _  -> return ()   -- Not a locally-bound thing, or
                               -- no cross-stage link
    }

--------------------------------------
checkCrossStageLifting :: TopLevelFlag -> Id -> ThStage -> TcM ()
-- If we are inside typed brackets, and (use_lvl > bind_lvl)
-- we must check whether there's a cross-stage lift to do
-- Examples   \x -> [|| x ||]
--            [|| map ||]
--
-- This is similar to checkCrossStageLifting in GHC.Rename.Splice, but
-- this code is applied to *typed* brackets.

checkCrossStageLifting top_lvl id (Brack _ (TcPending ps_var lie_var q))
  | isTopLevel top_lvl
  = when (isExternalName id_name) (keepAlive id_name)
    -- See Note [Keeping things alive for Template Haskell] in GHC.Rename.Splice

  | otherwise
  =     -- Nested identifiers, such as 'x' in
        -- E.g. \x -> [|| h x ||]
        -- We must behave as if the reference to x was
        --      h $(lift x)
        -- We use 'x' itself as the splice proxy, used by
        -- the desugarer to stitch it all back together.
        -- If 'x' occurs many times we may get many identical
        -- bindings of the same splice proxy, but that doesn't
        -- matter, although it's a mite untidy.
    do  { let id_ty = idType id
        ; checkTc (isTauTy id_ty) (polySpliceErr id)
               -- If x is polymorphic, its occurrence sites might
               -- have different instantiations, so we can't use plain
               -- 'x' as the splice proxy name.  I don't know how to
               -- solve this, and it's probably unimportant, so I'm
               -- just going to flag an error for now

        ; lift <- if isStringTy id_ty then
                     do { sid <- tcLookupId GHC.Builtin.Names.TH.liftStringName
                                     -- See Note [Lifting strings]
                        ; return (HsVar noExtField (noLocA sid)) }
                  else
                     setConstraintVar lie_var   $
                          -- Put the 'lift' constraint into the right LIE
                     newMethodFromName (OccurrenceOf id_name)
                                       GHC.Builtin.Names.TH.liftName
                                       [getRuntimeRep id_ty, id_ty]

                   -- Update the pending splices
        ; ps <- readMutVar ps_var
        ; let pending_splice = PendingTcSplice id_name
                                 (nlHsApp (mkLHsWrap (applyQuoteWrapper q)
                                                     (noLocA lift))
                                          (nlHsVar id))
        ; writeMutVar ps_var (pending_splice : ps)

        ; return () }
  where
    id_name = idName id

checkCrossStageLifting _ _ _ = return ()

polySpliceErr :: Id -> SDoc
polySpliceErr id
  = text "Can't splice the polymorphic local variable" <+> quotes (ppr id)

{-
Note [Lifting strings]
~~~~~~~~~~~~~~~~~~~~~~
If we see $(... [| s |] ...) where s::String, we don't want to
generate a mass of Cons (CharL 'x') (Cons (CharL 'y') ...)) etc.
So this conditional short-circuits the lifting mechanism to generate
(liftString "xy") in that case.  I didn't want to use overlapping instances
for the Lift class in TH.Syntax, because that can lead to overlapping-instance
errors in a polymorphic situation.

If this check fails (which isn't impossible) we get another chance; see
Note [Converting strings] in "GHC.ThToHs"

Local record selectors
~~~~~~~~~~~~~~~~~~~~~~
Record selectors for TyCons in this module are ordinary local bindings,
which show up as ATcIds rather than AGlobals.  So we need to check for
naughtiness in both branches.  c.f. TcTyClsBindings.mkAuxBinds.


************************************************************************
*                                                                      *
\subsection{Record bindings}
*                                                                      *
************************************************************************
-}

getFixedTyVars :: [FieldLabelString] -> [TyVar] -> [ConLike] -> TyVarSet
-- These tyvars must not change across the updates
getFixedTyVars upd_fld_occs univ_tvs cons
      = mkVarSet [tv1 | con <- cons
                      , let (u_tvs, _, eqspec, prov_theta
                             , req_theta, arg_tys, _)
                              = conLikeFullSig con
                            theta = eqSpecPreds eqspec
                                     ++ prov_theta
                                     ++ req_theta
                            flds = conLikeFieldLabels con
                            fixed_tvs = exactTyCoVarsOfTypes (map scaledThing fixed_tys)
                                    -- fixed_tys: See Note [Type of a record update]
                                        `unionVarSet` tyCoVarsOfTypes theta
                                    -- Universally-quantified tyvars that
                                    -- appear in any of the *implicit*
                                    -- arguments to the constructor are fixed
                                    -- See Note [Implicit type sharing]

                            fixed_tys = [ty | (fl, ty) <- zip flds arg_tys
                                            , not (flLabel fl `elem` upd_fld_occs)]
                      , (tv1,tv) <- univ_tvs `zip` u_tvs
                      , tv `elemVarSet` fixed_tvs ]

{-
Note [Disambiguating record fields]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When the -XDuplicateRecordFields extension is used, and the renamer
encounters a record selector or update that it cannot immediately
disambiguate (because it involves fields that belong to multiple
datatypes), it will defer resolution of the ambiguity to the
typechecker.  In this case, the `Ambiguous` constructor of
`AmbiguousFieldOcc` is used.

Consider the following definitions:

        data S = MkS { foo :: Int }
        data T = MkT { foo :: Int, bar :: Int }
        data U = MkU { bar :: Int, baz :: Int }

When the renamer sees `foo` as a selector or an update, it will not
know which parent datatype is in use.

For selectors, there are two possible ways to disambiguate:

1. Check if the pushed-in type is a function whose domain is a
   datatype, for example:

       f s = (foo :: S -> Int) s

       g :: T -> Int
       g = foo

    This is checked by `tcCheckRecSelId` when checking `HsRecFld foo`.

2. Check if the selector is applied to an argument that has a type
   signature, for example:

       h = foo (s :: S)

    This is checked by `tcApp`.


Updates are slightly more complex.  The `disambiguateRecordBinds`
function tries to determine the parent datatype in three ways:

1. Check for types that have all the fields being updated. For example:

        f x = x { foo = 3, bar = 2 }

   Here `f` must be updating `T` because neither `S` nor `U` have
   both fields. This may also discover that no possible type exists.
   For example the following will be rejected:

        f' x = x { foo = 3, baz = 3 }

2. Use the type being pushed in, if it is already a TyConApp. The
   following are valid updates to `T`:

        g :: T -> T
        g x = x { foo = 3 }

        g' x = x { foo = 3 } :: T

3. Use the type signature of the record expression, if it exists and
   is a TyConApp. Thus this is valid update to `T`:

        h x = (x :: T) { foo = 3 }


Note that we do not look up the types of variables being updated, and
no constraint-solving is performed, so for example the following will
be rejected as ambiguous:

     let bad (s :: S) = foo s

     let r :: T
         r = blah
     in r { foo = 3 }

     \r. (r { foo = 3 },  r :: T )

We could add further tests, of a more heuristic nature. For example,
rather than looking for an explicit signature, we could try to infer
the type of the argument to a selector or the record expression being
updated, in case we are lucky enough to get a TyConApp straight
away. However, it might be hard for programmers to predict whether a
particular update is sufficiently obvious for the signature to be
omitted. Moreover, this might change the behaviour of typechecker in
non-obvious ways.

See also Note [HsRecField and HsRecUpdField] in GHC.Hs.Pat.
-}

-- Given a RdrName that refers to multiple record fields, and the type
-- of its argument, try to determine the name of the selector that is
-- meant.
disambiguateSelector :: LocatedN RdrName -> Type -> TcM Name
disambiguateSelector lr@(L _ rdr) parent_type
 = do { fam_inst_envs <- tcGetFamInstEnvs
      ; case tyConOf fam_inst_envs parent_type of
          Nothing -> ambiguousSelector lr
          Just p  ->
            do { xs <- lookupParents rdr
               ; let parent = RecSelData p
               ; case lookup parent xs of
                   Just gre -> do { addUsedGRE True gre
                                  ; return (gre_name gre) }
                   Nothing  -> failWithTc (fieldNotInType parent rdr) } }

-- This field name really is ambiguous, so add a suitable "ambiguous
-- occurrence" error, then give up.
ambiguousSelector :: LocatedN RdrName -> TcM a
ambiguousSelector (L _ rdr)
  = do { addAmbiguousNameErr rdr
       ; failM }

-- | This name really is ambiguous, so add a suitable "ambiguous
-- occurrence" error, then continue
addAmbiguousNameErr :: RdrName -> TcM ()
addAmbiguousNameErr rdr
  = do { env <- getGlobalRdrEnv
       ; let gres = lookupGRE_RdrName rdr env
       ; setErrCtxt [] $ addNameClashErrRn rdr gres}

-- Disambiguate the fields in a record update.
-- See Note [Disambiguating record fields]
disambiguateRecordBinds :: LHsExpr GhcRn -> TcRhoType
                 -> [LHsRecUpdField GhcRn] -> ExpRhoType
                 -> TcM [LHsRecField' (AmbiguousFieldOcc GhcTc) (LHsExpr GhcRn)]
disambiguateRecordBinds record_expr record_rho rbnds res_ty
    -- Are all the fields unambiguous?
  = case mapM isUnambiguous rbnds of
                     -- If so, just skip to looking up the Ids
                     -- Always the case if DuplicateRecordFields is off
      Just rbnds' -> mapM lookupSelector rbnds'
      Nothing     -> -- If not, try to identify a single parent
        do { fam_inst_envs <- tcGetFamInstEnvs
             -- Look up the possible parents for each field
           ; rbnds_with_parents <- getUpdFieldsParents
           ; let possible_parents = map (map fst . snd) rbnds_with_parents
             -- Identify a single parent
           ; p <- identifyParent fam_inst_envs possible_parents
             -- Pick the right selector with that parent for each field
           ; checkNoErrs $ mapM (pickParent p) rbnds_with_parents }
  where
    -- Extract the selector name of a field update if it is unambiguous
    isUnambiguous :: LHsRecUpdField GhcRn -> Maybe (LHsRecUpdField GhcRn,Name)
    isUnambiguous x = case unLoc (hsRecFieldLbl (unLoc x)) of
                        Unambiguous sel_name _ -> Just (x, sel_name)
                        Ambiguous{}            -> Nothing

    -- Look up the possible parents and selector GREs for each field
    getUpdFieldsParents :: TcM [(LHsRecUpdField GhcRn
                                , [(RecSelParent, GlobalRdrElt)])]
    getUpdFieldsParents
      = fmap (zip rbnds) $ mapM
          (lookupParents . unLoc . hsRecUpdFieldRdr . unLoc)
          rbnds

    -- Given a the lists of possible parents for each field,
    -- identify a single parent
    identifyParent :: FamInstEnvs -> [[RecSelParent]] -> TcM RecSelParent
    identifyParent fam_inst_envs possible_parents
      = case foldr1 intersect possible_parents of
        -- No parents for all fields: record update is ill-typed
        []  -> failWithTc (noPossibleParents rbnds)

        -- Exactly one datatype with all the fields: use that
        [p] -> return p

        -- Multiple possible parents: try harder to disambiguate
        -- Can we get a parent TyCon from the pushed-in type?
        _:_ | Just p <- tyConOfET fam_inst_envs res_ty -> return (RecSelData p)

        -- Does the expression being updated have a type signature?
        -- If so, try to extract a parent TyCon from it
            | Just {} <- obviousSig (unLoc record_expr)
            , Just tc <- tyConOf fam_inst_envs record_rho
            -> return (RecSelData tc)

        -- Nothing else we can try...
        _ -> failWithTc badOverloadedUpdate

    -- Make a field unambiguous by choosing the given parent.
    -- Emits an error if the field cannot have that parent,
    -- e.g. if the user writes
    --     r { x = e } :: T
    -- where T does not have field x.
    pickParent :: RecSelParent
               -> (LHsRecUpdField GhcRn, [(RecSelParent, GlobalRdrElt)])
               -> TcM (LHsRecField' (AmbiguousFieldOcc GhcTc) (LHsExpr GhcRn))
    pickParent p (upd, xs)
      = case lookup p xs of
                      -- Phew! The parent is valid for this field.
                      -- Previously ambiguous fields must be marked as
                      -- used now that we know which one is meant, but
                      -- unambiguous ones shouldn't be recorded again
                      -- (giving duplicate deprecation warnings).
          Just gre -> do { unless (null (tail xs)) $ do
                             let L loc _ = hsRecFieldLbl (unLoc upd)
                             setSrcSpan loc $ addUsedGRE True gre
                         ; lookupSelector (upd, gre_name gre) }
                      -- The field doesn't belong to this parent, so report
                      -- an error but keep going through all the fields
          Nothing  -> do { addErrTc (fieldNotInType p
                                      (unLoc (hsRecUpdFieldRdr (unLoc upd))))
                         ; lookupSelector (upd, gre_name (snd (head xs))) }

    -- Given a (field update, selector name) pair, look up the
    -- selector to give a field update with an unambiguous Id
    lookupSelector :: (LHsRecUpdField GhcRn, Name)
                 -> TcM (LHsRecField' (AmbiguousFieldOcc GhcTc) (LHsExpr GhcRn))
    lookupSelector (L l upd, n)
      = do { i <- tcLookupId n
           ; let L loc af = hsRecFieldLbl upd
                 lbl      = rdrNameAmbiguousFieldOcc af
           ; return $ L l upd { hsRecFieldLbl
                          = L loc (Unambiguous i (L (noAnnSrcSpan loc) lbl)) } }


-- Extract the outermost TyCon of a type, if there is one; for
-- data families this is the representation tycon (because that's
-- where the fields live).
tyConOf :: FamInstEnvs -> TcSigmaType -> Maybe TyCon
tyConOf fam_inst_envs ty0
  = case tcSplitTyConApp_maybe ty of
      Just (tc, tys) -> Just (fstOf3 (tcLookupDataFamInst fam_inst_envs tc tys))
      Nothing        -> Nothing
  where
    (_, _, ty) = tcSplitSigmaTy ty0

-- Variant of tyConOf that works for ExpTypes
tyConOfET :: FamInstEnvs -> ExpRhoType -> Maybe TyCon
tyConOfET fam_inst_envs ty0 = tyConOf fam_inst_envs =<< checkingExpType_maybe ty0

-- For an ambiguous record field, find all the candidate record
-- selectors (as GlobalRdrElts) and their parents.
lookupParents :: RdrName -> RnM [(RecSelParent, GlobalRdrElt)]
lookupParents rdr
  = do { env <- getGlobalRdrEnv
       ; let gres = lookupGRE_RdrName rdr env
       ; mapM lookupParent gres }
  where
    lookupParent :: GlobalRdrElt -> RnM (RecSelParent, GlobalRdrElt)
    lookupParent gre = do { id <- tcLookupId (gre_name gre)
                          ; if isRecordSelector id
                              then return (recordSelectorTyCon id, gre)
                              else failWithTc (notSelector (gre_name gre)) }

-- A type signature on the argument of an ambiguous record selector or
-- the record expression in an update must be "obvious", i.e. the
-- outermost constructor ignoring parentheses.
obviousSig :: HsExpr GhcRn -> Maybe (LHsSigWcType GhcRn)
obviousSig (ExprWithTySig _ _ ty) = Just ty
obviousSig (HsPar _ p)          = obviousSig (unLoc p)
obviousSig _                    = Nothing


{-
Game plan for record bindings
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
1. Find the TyCon for the bindings, from the first field label.

2. Instantiate its tyvars and unify (T a1 .. an) with expected_ty.

For each binding field = value

3. Instantiate the field type (from the field label) using the type
   envt from step 2.

4  Type check the value using tcArg, passing the field type as
   the expected argument type.

This extends OK when the field types are universally quantified.
-}

tcRecordBinds
        :: ConLike
        -> [TcType]     -- Expected type for each field
        -> HsRecordBinds GhcRn
        -> TcM (HsRecordBinds GhcTc)

tcRecordBinds con_like arg_tys (HsRecFields rbinds dd)
  = do  { mb_binds <- mapM do_bind rbinds
        ; return (HsRecFields (catMaybes mb_binds) dd) }
  where
    fields = map flSelector $ conLikeFieldLabels con_like
    flds_w_tys = zipEqual "tcRecordBinds" fields arg_tys

    do_bind :: LHsRecField GhcRn (LHsExpr GhcRn)
            -> TcM (Maybe (LHsRecField GhcTc (LHsExpr GhcTc)))
    do_bind (L l fld@(HsRecField { hsRecFieldLbl = f
                                 , hsRecFieldArg = rhs }))

      = do { mb <- tcRecordField con_like flds_w_tys f rhs
           ; case mb of
               Nothing         -> return Nothing
               Just (f', rhs') -> return (Just (L l (fld { hsRecFieldLbl = f'
                                                          , hsRecFieldArg = rhs' }))) }

tcRecordUpd
        :: ConLike
        -> [TcType]     -- Expected type for each field
        -> [LHsRecField' (AmbiguousFieldOcc GhcTc) (LHsExpr GhcRn)]
        -> TcM [LHsRecUpdField GhcTc]

tcRecordUpd con_like arg_tys rbinds = fmap catMaybes $ mapM do_bind rbinds
  where
    fields = map flSelector $ conLikeFieldLabels con_like
    flds_w_tys = zipEqual "tcRecordUpd" fields arg_tys

    do_bind :: LHsRecField' (AmbiguousFieldOcc GhcTc) (LHsExpr GhcRn)
            -> TcM (Maybe (LHsRecUpdField GhcTc))
    do_bind (L l fld@(HsRecField { hsRecFieldLbl = L loc af
                                 , hsRecFieldArg = rhs }))
      = do { let lbl = rdrNameAmbiguousFieldOcc af
                 sel_id = selectorAmbiguousFieldOcc af
                 f = L loc (FieldOcc (idName sel_id) (L (noAnnSrcSpan loc) lbl))
           ; mb <- tcRecordField con_like flds_w_tys f rhs
           ; case mb of
               Nothing         -> return Nothing
               Just (f', rhs') ->
                 return (Just
                         (L l (fld { hsRecFieldLbl
                                      = L loc (Unambiguous
                                               (extFieldOcc (unLoc f'))
                                               (L (noAnnSrcSpan loc) lbl))
                                   , hsRecFieldArg = rhs' }))) }

tcRecordField :: ConLike -> Assoc Name Type
              -> LFieldOcc GhcRn -> LHsExpr GhcRn
              -> TcM (Maybe (LFieldOcc GhcTc, LHsExpr GhcTc))
tcRecordField con_like flds_w_tys (L loc (FieldOcc sel_name lbl)) rhs
  | Just field_ty <- assocMaybe flds_w_tys sel_name
      = addErrCtxt (fieldCtxt field_lbl) $
        do { rhs' <- tcCheckPolyExprNC rhs field_ty
           ; let field_id = mkUserLocal (nameOccName sel_name)
                                        (nameUnique sel_name)
                                        Many field_ty loc
                -- Yuk: the field_id has the *unique* of the selector Id
                --          (so we can find it easily)
                --      but is a LocalId with the appropriate type of the RHS
                --          (so the desugarer knows the type of local binder to make)
           ; return (Just (L loc (FieldOcc field_id lbl), rhs')) }
      | otherwise
      = do { addErrTc (badFieldCon con_like field_lbl)
           ; return Nothing }
  where
        field_lbl = occNameFS $ rdrNameOcc (unLoc lbl)


checkMissingFields ::  ConLike -> HsRecordBinds GhcRn -> TcM ()
checkMissingFields con_like rbinds
  | null field_labels   -- Not declared as a record;
                        -- But C{} is still valid if no strict fields
  = if any isBanged field_strs then
        -- Illegal if any arg is strict
        addErrTc (missingStrictFields con_like [])
    else do
        warn <- woptM Opt_WarnMissingFields
        when (warn && notNull field_strs && null field_labels)
             (warnTc (Reason Opt_WarnMissingFields) True
                 (missingFields con_like []))

  | otherwise = do              -- A record
    unless (null missing_s_fields)
           (addErrTc (missingStrictFields con_like missing_s_fields))

    warn <- woptM Opt_WarnMissingFields
    when (warn && notNull missing_ns_fields)
         (warnTc (Reason Opt_WarnMissingFields) True
             (missingFields con_like missing_ns_fields))

  where
    missing_s_fields
        = [ flLabel fl | (fl, str) <- field_info,
                 isBanged str,
                 not (fl `elemField` field_names_used)
          ]
    missing_ns_fields
        = [ flLabel fl | (fl, str) <- field_info,
                 not (isBanged str),
                 not (fl `elemField` field_names_used)
          ]

    field_names_used = hsRecFields rbinds
    field_labels     = conLikeFieldLabels con_like

    field_info = zipEqual "missingFields"
                          field_labels
                          field_strs

    field_strs = conLikeImplBangs con_like

    fl `elemField` flds = any (\ fl' -> flSelector fl == fl') flds

{-
************************************************************************
*                                                                      *
\subsection{Errors and contexts}
*                                                                      *
************************************************************************

Boring and alphabetical:
-}

fieldCtxt :: FieldLabelString -> SDoc
fieldCtxt field_name
  = text "In the" <+> quotes (ppr field_name) <+> ptext (sLit "field of a record")

addExprCtxt :: LHsExpr GhcRn -> TcRn a -> TcRn a
addExprCtxt e thing_inside = addErrCtxt (exprCtxt (unLoc e)) thing_inside

exprCtxt :: HsExpr GhcRn -> SDoc
exprCtxt expr = hang (text "In the expression:") 2 (ppr (stripParensHsExpr expr))

addFunResCtxt :: Bool  -- There is at least one argument
              -> HsExpr GhcTc -> TcType -> ExpRhoType
              -> TcM a -> TcM a
-- When we have a mis-match in the return type of a function
-- try to give a helpful message about too many/few arguments
--
-- Used for naked variables too; but with has_args = False
addFunResCtxt has_args fun fun_res_ty env_ty
  = addLandmarkErrCtxtM (\env -> (env, ) <$> mk_msg)
      -- NB: use a landmark error context, so that an empty context
      -- doesn't suppress some more useful context
  where
    mk_msg
      = do { mb_env_ty <- readExpType_maybe env_ty
                     -- by the time the message is rendered, the ExpType
                     -- will be filled in (except if we're debugging)
           ; fun_res' <- zonkTcType fun_res_ty
           ; env'     <- case mb_env_ty of
                           Just env_ty -> zonkTcType env_ty
                           Nothing     ->
                             do { dumping <- doptM Opt_D_dump_tc_trace
                                ; MASSERT( dumping )
                                ; newFlexiTyVarTy liftedTypeKind }
           ; let -- See Note [Splitting nested sigma types in mismatched
                 --           function types]
                 (_, _, fun_tau) = tcSplitNestedSigmaTys fun_res'
                 -- No need to call tcSplitNestedSigmaTys here, since env_ty is
                 -- an ExpRhoTy, i.e., it's already instantiated.
                 (_, _, env_tau) = tcSplitSigmaTy env'
                 (args_fun, res_fun) = tcSplitFunTys fun_tau
                 (args_env, res_env) = tcSplitFunTys env_tau
                 n_fun = length args_fun
                 n_env = length args_env
                 info  | n_fun == n_env = Outputable.empty
                       | n_fun > n_env
                       , not_fun res_env
                       = text "Probable cause:" <+> quotes (ppr fun)
                         <+> text "is applied to too few arguments"

                       | has_args
                       , not_fun res_fun
                       = text "Possible cause:" <+> quotes (ppr fun)
                         <+> text "is applied to too many arguments"

                       | otherwise
                       = Outputable.empty  -- Never suggest that a naked variable is                                         -- applied to too many args!
           ; return info }
      where
        not_fun ty   -- ty is definitely not an arrow type,
                     -- and cannot conceivably become one
          = case tcSplitTyConApp_maybe ty of
              Just (tc, _) -> isAlgTyCon tc
              Nothing      -> False

{-
Note [Splitting nested sigma types in mismatched function types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When one applies a function to too few arguments, GHC tries to determine this
fact if possible so that it may give a helpful error message. It accomplishes
this by checking if the type of the applied function has more argument types
than supplied arguments.

Previously, GHC computed the number of argument types through tcSplitSigmaTy.
This is incorrect in the face of nested foralls, however! This caused Trac
#13311, for instance:

  f :: forall a. (Monoid a) => forall b. (Monoid b) => Maybe a -> Maybe b

If one uses `f` like so:

  do { f; putChar 'a' }

Then tcSplitSigmaTy will decompose the type of `f` into:

  Tyvars: [a]
  Context: (Monoid a)
  Argument types: []
  Return type: forall b. Monoid b => Maybe a -> Maybe b

That is, it will conclude that there are *no* argument types, and since `f`
was given no arguments, it won't print a helpful error message. On the other
hand, tcSplitNestedSigmaTys correctly decomposes `f`'s type down to:

  Tyvars: [a, b]
  Context: (Monoid a, Monoid b)
  Argument types: [Maybe a]
  Return type: Maybe b

So now GHC recognizes that `f` has one more argument type than it was actually
provided.
-}

badFieldTypes :: [(FieldLabelString,TcType)] -> SDoc
badFieldTypes prs
  = hang (text "Record update for insufficiently polymorphic field"
                         <> plural prs <> colon)
       2 (vcat [ ppr f <+> dcolon <+> ppr ty | (f,ty) <- prs ])

badFieldsUpd
  :: [LHsRecField' (AmbiguousFieldOcc GhcTc) (LHsExpr GhcRn)]
               -- Field names that don't belong to a single datacon
  -> [ConLike] -- Data cons of the type which the first field name belongs to
  -> SDoc
badFieldsUpd rbinds data_cons
  = hang (text "No constructor has all these fields:")
       2 (pprQuotedList conflictingFields)
          -- See Note [Finding the conflicting fields]
  where
    -- A (preferably small) set of fields such that no constructor contains
    -- all of them.  See Note [Finding the conflicting fields]
    conflictingFields = case nonMembers of
        -- nonMember belongs to a different type.
        (nonMember, _) : _ -> [aMember, nonMember]
        [] -> let
            -- All of rbinds belong to one type. In this case, repeatedly add
            -- a field to the set until no constructor contains the set.

            -- Each field, together with a list indicating which constructors
            -- have all the fields so far.
            growingSets :: [(FieldLabelString, [Bool])]
            growingSets = scanl1 combine membership
            combine (_, setMem) (field, fldMem)
              = (field, zipWith (&&) setMem fldMem)
            in
            -- Fields that don't change the membership status of the set
            -- are redundant and can be dropped.
            map (fst . head) $ groupBy ((==) `on` snd) growingSets

    aMember = ASSERT( not (null members) ) fst (head members)
    (members, nonMembers) = partition (or . snd) membership

    -- For each field, which constructors contain the field?
    membership :: [(FieldLabelString, [Bool])]
    membership = sortMembership $
        map (\fld -> (fld, map (Set.member fld) fieldLabelSets)) $
          map (occNameFS . rdrNameOcc . rdrNameAmbiguousFieldOcc . unLoc . hsRecFieldLbl . unLoc) rbinds

    fieldLabelSets :: [Set.Set FieldLabelString]
    fieldLabelSets = map (Set.fromList . map flLabel . conLikeFieldLabels) data_cons

    -- Sort in order of increasing number of True, so that a smaller
    -- conflicting set can be found.
    sortMembership =
      map snd .
      sortBy (compare `on` fst) .
      map (\ item@(_, membershipRow) -> (countTrue membershipRow, item))

    countTrue = count id

{-
Note [Finding the conflicting fields]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we have
  data A = A {a0, a1 :: Int}
         | B {b0, b1 :: Int}
and we see a record update
  x { a0 = 3, a1 = 2, b0 = 4, b1 = 5 }
Then we'd like to find the smallest subset of fields that no
constructor has all of.  Here, say, {a0,b0}, or {a0,b1}, etc.
We don't really want to report that no constructor has all of
{a0,a1,b0,b1}, because when there are hundreds of fields it's
hard to see what was really wrong.

We may need more than two fields, though; eg
  data T = A { x,y :: Int, v::Int }
          | B { y,z :: Int, v::Int }
          | C { z,x :: Int, v::Int }
with update
   r { x=e1, y=e2, z=e3 }, we

Finding the smallest subset is hard, so the code here makes
a decent stab, no more.  See #7989.
-}

naughtyRecordSel :: RdrName -> SDoc
naughtyRecordSel sel_id
  = text "Cannot use record selector" <+> quotes (ppr sel_id) <+>
    text "as a function due to escaped type variables" $$
    text "Probable fix: use pattern-matching syntax instead"

notSelector :: Name -> SDoc
notSelector field
  = hsep [quotes (ppr field), text "is not a record selector"]

mixedSelectors :: [Id] -> [Id] -> SDoc
mixedSelectors data_sels@(dc_rep_id:_) pat_syn_sels@(ps_rep_id:_)
  = ptext
      (sLit "Cannot use a mixture of pattern synonym and record selectors") $$
    text "Record selectors defined by"
      <+> quotes (ppr (tyConName rep_dc))
      <> text ":"
      <+> pprWithCommas ppr data_sels $$
    text "Pattern synonym selectors defined by"
      <+> quotes (ppr (patSynName rep_ps))
      <> text ":"
      <+> pprWithCommas ppr pat_syn_sels
  where
    RecSelPatSyn rep_ps = recordSelectorTyCon ps_rep_id
    RecSelData rep_dc = recordSelectorTyCon dc_rep_id
mixedSelectors _ _ = panic "GHC.Tc.Gen.Expr: mixedSelectors emptylists"


missingStrictFields :: ConLike -> [FieldLabelString] -> SDoc
missingStrictFields con fields
  = header <> rest
  where
    rest | null fields = Outputable.empty  -- Happens for non-record constructors
                                           -- with strict fields
         | otherwise   = colon <+> pprWithCommas ppr fields

    header = text "Constructor" <+> quotes (ppr con) <+>
             text "does not have the required strict field(s)"

missingFields :: ConLike -> [FieldLabelString] -> SDoc
missingFields con fields
  = header <> rest
  where
    rest | null fields = Outputable.empty
         | otherwise = colon <+> pprWithCommas ppr fields
    header = text "Fields of" <+> quotes (ppr con) <+>
             text "not initialised"

-- callCtxt fun args = text "In the call" <+> parens (ppr (foldl' mkHsApp fun args))

noPossibleParents :: [LHsRecUpdField GhcRn] -> SDoc
noPossibleParents rbinds
  = hang (text "No type has all these fields:")
       2 (pprQuotedList fields)
  where
    fields = map (hsRecFieldLbl . unLoc) rbinds

badOverloadedUpdate :: SDoc
badOverloadedUpdate = text "Record update is ambiguous, and requires a type signature"

fieldNotInType :: RecSelParent -> RdrName -> SDoc
fieldNotInType p rdr
  = unknownSubordinateErr (text "field of type" <+> quotes (ppr p)) rdr

{-
************************************************************************
*                                                                      *
\subsection{Static Pointers}
*                                                                      *
************************************************************************
-}

-- | A data type to describe why a variable is not closed.
data NotClosedReason = NotLetBoundReason
                     | NotTypeClosed VarSet
                     | NotClosed Name NotClosedReason

-- | Checks if the given name is closed and emits an error if not.
--
-- See Note [Not-closed error messages].
checkClosedInStaticForm :: Name -> TcM ()
checkClosedInStaticForm name = do
    type_env <- getLclTypeEnv
    case checkClosed type_env name of
      Nothing -> return ()
      Just reason -> addErrTc $ explain name reason
  where
    -- See Note [Checking closedness].
    checkClosed :: TcTypeEnv -> Name -> Maybe NotClosedReason
    checkClosed type_env n = checkLoop type_env (unitNameSet n) n

    checkLoop :: TcTypeEnv -> NameSet -> Name -> Maybe NotClosedReason
    checkLoop type_env visited n = do
      -- The @visited@ set is an accumulating parameter that contains the set of
      -- visited nodes, so we avoid repeating cycles in the traversal.
      case lookupNameEnv type_env n of
        Just (ATcId { tct_id = tcid, tct_info = info }) -> case info of
          ClosedLet   -> Nothing
          NotLetBound -> Just NotLetBoundReason
          NonClosedLet fvs type_closed -> listToMaybe $
            -- Look for a non-closed variable in fvs
            [ NotClosed n' reason
            | n' <- nameSetElemsStable fvs
            , not (elemNameSet n' visited)
            , Just reason <- [checkLoop type_env (extendNameSet visited n') n']
            ] ++
            if type_closed then
              []
            else
              -- We consider non-let-bound variables easier to figure out than
              -- non-closed types, so we report non-closed types to the user
              -- only if we cannot spot the former.
              [ NotTypeClosed $ tyCoVarsOfType (idType tcid) ]
        -- The binding is closed.
        _ -> Nothing

    -- Converts a reason into a human-readable sentence.
    --
    -- @explain name reason@ starts with
    --
    -- "<name> is used in a static form but it is not closed because it"
    --
    -- and then follows a list of causes. For each id in the path, the text
    --
    -- "uses <id> which"
    --
    -- is appended, yielding something like
    --
    -- "uses <id> which uses <id1> which uses <id2> which"
    --
    -- until the end of the path is reached, which is reported as either
    --
    -- "is not let-bound"
    --
    -- when the final node is not let-bound, or
    --
    -- "has a non-closed type because it contains the type variables:
    -- v1, v2, v3"
    --
    -- when the final node has a non-closed type.
    --
    explain :: Name -> NotClosedReason -> SDoc
    explain name reason =
      quotes (ppr name) <+> text "is used in a static form but it is not closed"
                        <+> text "because it"
                        $$
                        sep (causes reason)

    causes :: NotClosedReason -> [SDoc]
    causes NotLetBoundReason = [text "is not let-bound."]
    causes (NotTypeClosed vs) =
      [ text "has a non-closed type because it contains the"
      , text "type variables:" <+>
        pprVarSet vs (hsep . punctuate comma . map (quotes . ppr))
      ]
    causes (NotClosed n reason) =
      let msg = text "uses" <+> quotes (ppr n) <+> text "which"
       in case reason of
            NotClosed _ _ -> msg : causes reason
            _   -> let (xs0, xs1) = splitAt 1 $ causes reason
                    in fmap (msg <+>) xs0 ++ xs1

-- Note [Not-closed error messages]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- When variables in a static form are not closed, we go through the trouble
-- of explaining why they aren't.
--
-- Thus, the following program
--
-- > {-# LANGUAGE StaticPointers #-}
-- > module M where
-- >
-- > f x = static g
-- >   where
-- >     g = h
-- >     h = x
--
-- produces the error
--
--    'g' is used in a static form but it is not closed because it
--    uses 'h' which uses 'x' which is not let-bound.
--
-- And a program like
--
-- > {-# LANGUAGE StaticPointers #-}
-- > module M where
-- >
-- > import Data.Typeable
-- > import GHC.StaticPtr
-- >
-- > f :: Typeable a => a -> StaticPtr TypeRep
-- > f x = const (static (g undefined)) (h x)
-- >   where
-- >     g = h
-- >     h = typeOf
--
-- produces the error
--
--    'g' is used in a static form but it is not closed because it
--    uses 'h' which has a non-closed type because it contains the
--    type variables: 'a'
--

-- Note [Checking closedness]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- @checkClosed@ checks if a binding is closed and returns a reason if it is
-- not.
--
-- The bindings define a graph where the nodes are ids, and there is an edge
-- from @id1@ to @id2@ if the rhs of @id1@ contains @id2@ among its free
-- variables.
--
-- When @n@ is not closed, it has to exist in the graph some node reachable
-- from @n@ that it is not a let-bound variable or that it has a non-closed
-- type. Thus, the "reason" is a path from @n@ to this offending node.
--
-- When @n@ is not closed, we traverse the graph reachable from @n@ to build
-- the reason.
--
