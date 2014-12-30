{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

\section[TcMonoType]{Typechecking user-specified @MonoTypes@}
-}

{-# LANGUAGE CPP #-}

module TcHsType (
        tcHsSigType, tcHsSigTypeNC, tcHsDeriv, tcHsVectInst,
        tcHsInstHead, 
        UserTypeCtxt(..), 

                -- Type checking type and class decls
        kcLookupKind, kcTyClTyVars, tcTyClTyVars,
        tcHsConArgType, tcDataKindSig, 
        tcClassSigType,

                -- Kind-checking types
                -- No kind generalisation, no checkValidType
        kcHsTyVarBndrs, tcHsTyVarBndrs, 
        tcHsLiftedType, tcHsOpenType,
        tcLHsType, tcCheckLHsType, 
        tcHsContext, tcInferApps, tcHsTelescope,

        kindGeneralize,

                -- Sort-checking kinds
        tcLHsKind, 

                -- Pattern type signatures
        tcHsPatSigType, tcPatSig
   ) where

#include "HsVersions.h"

import HsSyn hiding ( Implicit, Explicit )
import TcRnMonad
import TcEvidence( HsWrapper )
import TcEnv
import TcMType
import TcValidity
import TcUnify
import TcIface
import TcHsSyn ( zonkCoToCo, emptyZonkEnv )  -- TODO (RAE): Remove!
import TcType
import Type
import TyCoRep( Type(..), Binder(..) ) 
import Kind
import RdrName( lookupLocalRdrOcc )
import Var
import VarSet
import TyCon
import ConLike
import DataCon
import TysPrim ( tYPE )
import Class
import Name
import NameEnv
import TysWiredIn
import BasicTypes
import SrcLoc
import DynFlags ( ExtensionFlag( Opt_DataKinds ) )
import Unique
import Util
import UniqSupply
import Outputable
import FastString
import PrelNames
import Maybes

import Control.Monad
import Data.List

{-
        ----------------------------
                General notes
        ----------------------------

Unlike with expressions, type-checking types both does some checking and
desugars at the same time. This is necessary because we often want to perform
equality checks on the types right away, and it would be incredibly painful
to do this on un-desugared types. Luckily, desugared types are close enough
to HsTypes to make the error messages sane.

During type-checking, we perform as little validity checking as possible.
This is because some type-checking is done in a mutually-recursive knot, and
if we look too closely at the tycons, we'll loop. This is why we always must
use mkNakedTyConApp and mkNakedAppTys, etc., which never look at a tycon.
The mkNamed... functions don't uphold Type invariants, but zonkTcTypeToType
will repair this for us. Note that zonkTcType *is* safe within a knot, and
can be done repeatedly with no ill effect: it just squeezes out metavariables.

Generally, after type-checking, you will want to do validity checking, say
with TcValidity.checkValidType.

Validity checking
~~~~~~~~~~~~~~~~~
Some of the validity check could in principle be done by the kind checker, 
but not all:

- During desugaring, we normalise by expanding type synonyms.  Only
  after this step can we check things like type-synonym saturation
  e.g.  type T k = k Int
        type S a = a
  Then (T S) is ok, because T is saturated; (T S) expands to (S Int);
  and then S is saturated.  This is a GHC extension.

- Similarly, also a GHC extension, we look through synonyms before complaining
  about the form of a class or instance declaration

- Ambiguity checks involve functional dependencies, and it's easier to wait
  until knots have been resolved before poking into them

Also, in a mutually recursive group of types, we can't look at the TyCon until we've
finished building the loop.  So to keep things simple, we postpone most validity
checking until step (3).

Knot tying
~~~~~~~~~~
During step (1) we might fault in a TyCon defined in another module, and it might
(via a loop) refer back to a TyCon defined in this module. So when we tie a big
knot around type declarations with ARecThing, so that the fault-in code can get
the TyCon being defined.

%************************************************************************
%*                                                                      *
              Check types AND do validity checking
*                                                                      *
************************************************************************
-}

tcHsSigType, tcHsSigTypeNC :: UserTypeCtxt -> LHsType Name -> TcM Type
  -- NB: it's important that the foralls that come from the top-level
  --     HsForAllTy in hs_ty occur *first* in the returned type.
  --     See Note [Scoped] with TcSigInfo
tcHsSigType ctxt hs_ty
  = addErrCtxt (pprSigCtxt ctxt empty (ppr hs_ty)) $
    tcHsSigTypeNC ctxt hs_ty

tcHsSigTypeNC ctxt (L loc hs_ty)
  = setSrcSpan loc $    -- The "In the type..." context
                        -- comes from the caller; hence "NC"
    do  { kind <- case expectedKindInCtxt ctxt of
                    AnythingKind -> newMetaKindVar
                    TheKind k    -> return k
                    OpenKind     -> do { lev <- newFlexiTyVarTy levityTy
                                       ; return $ tYPE lev }
          -- The kind is checked by checkValidType, and isn't necessarily
          -- of kind * in a Template Haskell quote eg [t| Maybe |]

          -- Generalise here: see Note [Kind generalisation]
        ; ty <- tcCheckHsTypeAndGen hs_ty kind

          -- Zonk to expose kind information to checkValidType
        ; ty <- zonkSigType ty
        ; checkValidType ctxt ty
        ; return ty }

-----------------
tcHsInstHead :: UserTypeCtxt -> LHsType Name -> TcM ([TyCoVar], ThetaType, Class, [Type])
-- Like tcHsSigTypeNC, but for an instance head.
tcHsInstHead user_ctxt lhs_ty@(L loc hs_ty)
  = setSrcSpan loc $    -- The "In the type..." context comes from the caller
    do { inst_ty <- tc_inst_head hs_ty
       ; kvs     <- zonkTcTypeAndFV inst_ty
       ; kvs     <- kindGeneralize kvs
       ; inst_ty <- zonkSigType (mkInvForAllTys kvs inst_ty)
       ; checkValidInstance user_ctxt lhs_ty inst_ty }

tc_inst_head :: HsType Name -> TcM TcType
tc_inst_head (HsForAllTy _ _ hs_tvs hs_ctxt hs_ty)
  = tcHsTyVarBndrs hs_tvs $ \ tvs ->
    do { ctxt <- tcHsContext hs_ctxt
       ; ty   <- tc_lhs_type hs_ty constraintKind    -- Body for forall has kind Constraint
                  -- TODO (RAE): This will be changed with "forall ->" syntax
       ; return (mkInvSigmaTy tvs ctxt ty) }

tc_inst_head hs_ty
  = tc_hs_type hs_ty constraintKind

-----------------
tcHsDeriv :: HsType Name -> TcM ([TyCoVar], Class, [Type], Kind)
-- Like tcHsSigTypeNC, but for the ...deriving( C t1 ty2 ) clause
-- Returns the C, [ty1, ty2, and the kind of C's *next* argument
-- E.g.    class C (a::*) (b::k->k)
--         data T a b = ... deriving( C Int )
--    returns ([k], C, [k, Int],  k->k)
-- Also checks that (C ty1 ty2 arg) :: Constraint
-- if arg has a suitable kind
tcHsDeriv hs_ty
  = do { arg_kind <- newMetaKindVar
       ; ty <- tcCheckHsTypeAndGen hs_ty (mkArrowKind arg_kind constraintKind)
       ; ty       <- zonkSigType ty
       ; arg_kind <- zonkSigType arg_kind
       ; let (tvs, pred) = splitNamedForAllTys ty
       ; case getClassPredTys_maybe pred of
           Just (cls, tys) -> return (tvs, cls, tys, arg_kind)
           Nothing -> failWithTc (ptext (sLit "Illegal deriving item") <+> quotes (ppr hs_ty)) }

-- Used for 'VECTORISE [SCALAR] instance' declarations
--
tcHsVectInst :: LHsType Name -> TcM (Class, [Type])
tcHsVectInst ty
  | Just (L _ cls_name, tys) <- splitLHsClassTy_maybe ty
  = do { (cls, cls_kind) <- tcClass cls_name
       ; (arg_tys, _res_kind) <- tcInferApps cls_name cls_kind tys
       ; return (cls, arg_tys) }
  | otherwise
  = failWithTc $ ptext (sLit "Malformed instance type")

{-
        These functions are used during knot-tying in
        type and class declarations, when we have to
        separate kind-checking, desugaring, and validity checking


************************************************************************
*                                                                      *
            The main kind checker: no validity checks here
%*                                                                      *
%************************************************************************
        
        First a couple of simple wrappers for kcHsType
-}

tcClassSigType :: LHsType Name -> TcM Type
tcClassSigType lhs_ty@(L _ hs_ty)
  = addTypeCtxt lhs_ty $
    do { ty <- tcCheckHsTypeAndGen hs_ty liftedTypeKind
       ; zonkSigType ty }

tcHsConArgType :: NewOrData ->  LHsType Name -> TcM Type
-- Permit a bang, but discard it
tcHsConArgType NewType  bty = tcHsLiftedType (getBangType bty)
  -- Newtypes can't have bangs, but we don't check that
  -- until checkValidDataCon, so do not want to crash here

tcHsConArgType DataType bty = tcHsOpenType (getBangType bty)
  -- Can't allow an unlifted type for newtypes, because we're effectively
  -- going to remove the constructor while coercing it to a lifted type.
  -- And newtypes can't be bang'd

---------------------------
tcHsTelescope :: SDoc -> [LHsType Name] -> [Binder] -> TcM [TcType]
tcHsTelescope what = go 1 emptyTCvSubst
  where
    go n subst (hs_ty : hs_tys) (bndr : bndrs)
      = do { ty <- addTypeCtxt hs_ty $
                   tc_lhs_type hs_ty (substTy subst (binderType bndr))
           ; let subst' = case binderVar_maybe bndr of
                            Just tv -> extendTCvSubst subst tv ty
                            Nothing -> subst
           ; tys <- go (n+1) subst' hs_tys bndrs
           ; return (ty : tys) }
    go n _ (hs_ty : _) [] =
      addErrTc (hang (text "Too many parameters to" <+> what <> colon)
                   2 (vcat [ ppr hs_ty <+> text "is unexpected;"
                           , text "expected only" <+> (ppr (n-1))
                             <+> text "parameter" <> plural_n ]))
      >> return []  -- won't cause panic later
      where plural_n
              | n-1 == 1  = empty
              | otherwise = char 's'
    go n _ [] bndrs@(_:_) =
      addErrTc (text "Not enough parameters to" <+> what <> semi
                <+> text "expected" <+> (ppr (n + length bndrs - 1))
                <+> text "but got" <+> (ppr (n-1)))
      >> return []
                   
    go _ _ _ _ = return []

tcHsArgTys :: [LHsType Name] -> [Kind] -> TcM [TcType]
tcHsArgTys tys kinds = zipWithM tc_lhs_type tys kinds

---------------------------
tcHsOpenType, tcHsLiftedType :: LHsType Name -> TcM TcType
-- Used for type signatures
-- Do not do validity checking
tcHsOpenType ty
  = addTypeCtxt ty $
    do { ek <- ekOpen
       ; tc_lhs_type ty ek }
tcHsLiftedType ty = addTypeCtxt ty $ tc_lhs_type ty liftedTypeKind

-- Like tcHsType, but takes an expected kind
tcCheckLHsType :: LHsType Name -> Kind -> TcM Type
tcCheckLHsType hs_ty exp_kind
  = addTypeCtxt hs_ty $ 
    tc_lhs_type hs_ty exp_kind

tcLHsType :: LHsType Name -> TcM (TcType, TcKind)
-- Called from outside: set the context
tcLHsType ty = addTypeCtxt ty (tc_infer_lhs_type ty)

---------------------------
tcCheckHsTypeAndGen :: HsType Name -> Kind -> TcM Type
-- Input type is HsType, not LhsType; the caller adds the context
-- Typecheck a type signature, and kind-generalise it
-- The result is not necessarily zonked, and has not been checked for validity
tcCheckHsTypeAndGen hs_ty kind
  = do { ty  <- tc_hs_type hs_ty kind
       ; traceTc "tcCheckHsTypeAndGen" (ppr hs_ty)
       ; kvs <- zonkTcTypeAndFV ty 
       ; kvs <- kindGeneralize kvs
       ; return (mkInvForAllTys kvs ty) }

{-
Note [Bidirectional type checking]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In expressions, whenever we see a polymorphic identifier, say `id`, we are
free to instantiate it with metavariables, knowing that we can always
re-generalize with type-lambdas when necessary. For example:

  rank2 :: (forall a. a -> a) -> ()
  x = rank2 id

When checking the body of `x`, we can instantiate `id` with a metavariable.
Then, when we're checking the application of `rank2`, we notice that we really
need a polymorphic `id`, and then re-generalize over the unconstrained
metavariable.

In types, however, we're not so lucky, because *we cannot re-generalize*!
There is no lambda. So, we must be careful only to instantiate at the last
possible moment, when we're sure we're never going to want the lost polymorphism
again.

To implement this behavior, we use bidirectional type checking, where we
explicitly think about whether we know the kind of the type we're checking
or not. Note that there is a difference between not knowing a kind and
knowing a metavariable kind: the metavariables are TauTvs, and cannot become
forall-quantified kinds. Previously (before dependent types), there were
no higher-rank kinds, and so we could instantiate early and be sure that
no types would have polymorphic kinds, and so we could always assume that
the kind of a type was a fresh metavariable. Not so anymore, thus the
need for two algorithms.

For HsType forms that can never be kind-polymorphic, we implement only the
"down" direction, where we safely assume a metavariable kind. For HsType forms
that *can* be kind-polymorphic, we implement just the "up" (functions with
"infer" in their name) version, as we gain nothing by also implementing the
"down" version.

Note [Future-proofing the type checker]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As discussed in Note [Bidirectional type checking], each HsType form is
handled in *either* tc_infer_hs_type *or* tc_hs_type. These functions
are mutually recursive, so that either one can work for any type former.
But, we want to make sure that our pattern-matches are complete. So,
we have a bunch of repetitive code just so that we get warnings if we're
missing any patterns.
-}

-- | Check and desugar a type, returning the core type and its
-- possibly-polymorphic kind. Much like 'tcInferRho' at the expression
-- level.
tc_infer_lhs_type :: LHsType Name -> TcM (TcType, TcKind)
tc_infer_lhs_type (L span ty)
  = setSrcSpan span $
    do { traceTc "tc_infer_lhs_type:" (ppr ty)
       ; tc_infer_hs_type ty }

-- | Infer the kind of a type and desugar. This is the "up" type-checker,
-- as described in Note [Bidirectional type checking]
tc_infer_hs_type :: HsType Name -> TcM (TcType, TcKind)
tc_infer_hs_type (HsTyVar tv)    = tcTyVar tv
tc_infer_hs_type (HsAppTy ty1 ty2)
  = do { let (fun_ty, arg_tys) = splitHsAppTys ty1 [ty2]
       ; (fun_ty', fun_kind) <- tc_infer_lhs_type fun_ty
       ; fun_kind' <- zonkTcType fun_kind
       ; (arg_tys', res_kind) <- tcInferApps fun_ty fun_kind' arg_tys
       ; return (mkNakedAppTys fun_ty' arg_tys', res_kind) }
tc_infer_hs_type (HsParTy t)     = tc_infer_lhs_type t
tc_infer_hs_type (HsOpTy lhs l_op@(L _ op) rhs)
  | not (op `hasKey` funTyConKey)
  = do { (op', op_kind) <- tcTyVar op
       ; op_kind' <- zonkTcType op_kind
       ; (arg_tys', res_kind) <- tcInferApps l_op op_kind' [lhs, rhs]
       ; return (mkNakedAppTys op' arg_tys', res_kind) }
tc_infer_hs_type (HsKindSig ty sig)
  = do { sig' <- tcLHsKind sig
       ; ty' <- tc_lhs_type ty sig'
       ; return (ty', sig') }
tc_infer_hs_type (HsDocTy ty _) = tc_infer_lhs_type ty
tc_infer_hs_type (HsCoreTy ty)  = return (ty, typeKind ty)
tc_infer_hs_type other_ty
  = do { kv <- newMetaKindVar
       ; ty' <- tc_hs_type other_ty kv
       ; return (ty', kv) }

tc_lhs_type :: LHsType Name -> TcKind -> TcM TcType
tc_lhs_type (L span ty) exp_kind
  = setSrcSpan span $
    do { traceTc "tc_lhs_type:" (ppr ty $$ ppr exp_kind)
       ; tc_hs_type ty exp_kind }

------------------------------------------
tc_fun_type :: LHsType Name -> LHsType Name -> TcKind -> TcM TcType
-- We need to recognise (->) so that we can construct a FunTy, 
-- *and* we need to do by looking at the Name, not the TyCon
-- (see Note [Zonking inside the knot]).  For example,
-- consider  f :: (->) Int Int  (Trac #7312)
tc_fun_type ty1 ty2 exp_kind
  = do { arg_lev <- newFlexiTyVarTy levityTy
       ; res_lev <- newFlexiTyVarTy levityTy
       ; ty1' <- tc_lhs_type ty1 (tYPE arg_lev)
       ; ty2' <- tc_lhs_type ty2 (tYPE res_lev)
       ; checkExpectedKind (mkFunTy ty1' ty2') liftedTypeKind exp_kind }

------------------------------------------
tc_hs_type :: HsType Name -> TcKind -> TcM TcType
tc_hs_type (HsParTy ty)        exp_kind = tc_lhs_type ty exp_kind
tc_hs_type (HsDocTy ty _)      exp_kind = tc_lhs_type ty exp_kind
tc_hs_type (HsQuasiQuoteTy {}) _ = panic "tc_hs_type: qq"       -- Eliminated by renamer
tc_hs_type ty@(HsBangTy {})    _
    -- While top-level bangs at this point are eliminated (eg !(Maybe Int)),
    -- other kinds of bangs are not (eg ((!Maybe) Int)). These kinds of
    -- bangs are invalid, so fail. (#7210)
    = failWithTc (ptext (sLit "Unexpected strictness annotation:") <+> ppr ty)
tc_hs_type (HsRecTy _)         _ = panic "tc_hs_type: record" -- Unwrapped by con decls
      -- Record types (which only show up temporarily in constructor 
      -- signatures) should have been removed by now

-- This should never happen; type splices are expanded by the renamer
tc_hs_type ty@(HsSpliceTy {}) _exp_kind
  = failWithTc (ptext (sLit "Unexpected type splice:") <+> ppr ty)

---------- Functions and applications
tc_hs_type (HsFunTy ty1 ty2) exp_kind
  = tc_fun_type ty1 ty2 exp_kind

tc_hs_type (HsOpTy ty1 (L _ op) ty2) exp_kind
  | op `hasKey` funTyConKey
  = tc_fun_type ty1 ty2 exp_kind

--------- Foralls
tc_hs_type hs_ty@(HsForAllTy _ _ hs_tvs context ty) exp_kind
  | isConstraintKind exp_kind
  = failWithTc (hang (ptext (sLit "Illegal constraint:")) 2 (ppr hs_ty))

  | otherwise
  = tcHsTyVarBndrs hs_tvs $ \ tvs' ->
    -- Do not kind-generalise here!  See Note [Kind generalisation]
    do { ctxt' <- tcHsContext context
       ; if null (unLoc context) then  -- Plain forall, no context
         do { ty' <- tc_lhs_type ty exp_kind
                -- Why exp_kind?  See Note [Body kind of forall]
            ; return $ mkInvSigmaTy tvs' ctxt' ty' }
         else
           -- If there is a context, then this forall is really a
           -- _function_, so the kind of the result really is *
           -- The body kind (result of the function) can be * or #, hence ekOpen
         do { ek  <- ekOpen
            ; ty' <- tc_lhs_type ty ek
            ; checkExpectedKind (mkInvSigmaTy tvs' ctxt' ty')
                                liftedTypeKind exp_kind } }
         -- TODO (RAE): Change this when "forall ->" syntax exists

--------- Lists, arrays, and tuples
tc_hs_type (HsListTy elt_ty) exp_kind 
  = do { tau_ty <- tc_lhs_type elt_ty liftedTypeKind
       ; checkWiredInTyCon listTyCon
       ; checkExpectedKind (mkListTy tau_ty) liftedTypeKind exp_kind }

tc_hs_type (HsPArrTy elt_ty) exp_kind
  = do { tau_ty <- tc_lhs_type elt_ty liftedTypeKind
       ; checkWiredInTyCon parrTyCon
       ; checkExpectedKind (mkPArrTy tau_ty) liftedTypeKind exp_kind }

-- See Note [Distinguishing tuple kinds] in HsTypes
-- See Note [Inferring tuple kinds]
tc_hs_type (HsTupleTy HsBoxedOrConstraintTuple hs_tys) exp_kind
     -- (NB: not zonking before looking at exp_k, to avoid left-right bias)
  | Just tup_sort <- tupKindSort_maybe exp_kind
  = traceTc "tc_hs_type tuple" (ppr hs_tys) >>
    tc_tuple tup_sort hs_tys exp_kind
  | otherwise
  = do { traceTc "tc_hs_type tuple 2" (ppr hs_tys)
       ; (tys, kinds) <- mapAndUnzipM tc_infer_lhs_type hs_tys
       ; kinds <- mapM zonkTcType kinds
           -- Infer each arg type separately, because errors can be
           -- confusing if we give them a shared kind.  Eg Trac #7410
           -- (Either Int, Int), we do not want to get an error saying
           -- "the second argument of a tuple should have kind *->*"

       ; let (arg_kind, tup_sort)
               = case [ (k,s) | k <- kinds
                              , Just s <- [tupKindSort_maybe k] ] of
                    ((k,s) : _) -> (k,s)
                    [] -> (liftedTypeKind, BoxedTuple)
         -- In the [] case, it's not clear what the kind is, so guess *

       ; tys' <- sequence [ setSrcSpan loc $
                            checkExpectedKind ty kind arg_kind
                          | ((L loc _),ty,kind) <- zip3 hs_tys tys kinds ]

       ; finish_tuple tup_sort tys' exp_kind }


tc_hs_type (HsTupleTy hs_tup_sort tys) exp_kind
  = tc_tuple tup_sort tys exp_kind
  where
    tup_sort = case hs_tup_sort of  -- Fourth case dealt with above
                  HsUnboxedTuple    -> UnboxedTuple
                  HsBoxedTuple      -> BoxedTuple
                  HsConstraintTuple -> ConstraintTuple
                  _                 -> panic "tc_hs_type HsTupleTy"


--------- Promoted lists and tuples
-- TODO (RAE): make this work with impredicative kinds by using
-- matchExpectedListTy
tc_hs_type (HsExplicitListTy _k tys) exp_kind
  = do { tks <- mapM tc_infer_lhs_type tys
       ; (taus', kind) <- unifyKinds tks
       ; let ty = (foldr (mk_cons kind) (mk_nil kind) taus')
       ; checkExpectedKind ty (mkListTy kind) exp_kind }
  where
    mk_cons k a b = mkTyConApp (promoteDataCon consDataCon) [k, a, b]
    mk_nil  k     = mkTyConApp (promoteDataCon nilDataCon) [k]

tc_hs_type (HsExplicitTupleTy _ tys) exp_kind
  = do { tks <- mapM tc_infer_lhs_type tys
       ; let n          = length tys
             kind_con   = tupleTyCon   BoxedTuple n
             ty_con     = promotedTupleDataCon BoxedTuple n
             (taus, ks) = unzip tks
             tup_k      = mkTyConApp kind_con ks
       ; checkExpectedKind (mkTyConApp ty_con (ks ++ taus)) tup_k exp_kind }

--------- Constraint types
tc_hs_type (HsIParamTy n ty) exp_kind
  = do { ty' <- tc_lhs_type ty liftedTypeKind
       ; ipClass <- tcLookupClass ipClassName
       ; let n' = mkStrLitTy $ hsIPNameFS n
       ; checkExpectedKind (mkClassPred ipClass [n',ty'])
           constraintKind exp_kind }

-- In the ~ case, we want to be careful with checkExpectedKind. checkExpectedKind
-- can do implicit argument instantiation. But, we don't know which argument
-- to ~ might need the instantiation. So, we compare lists of implicit
-- arguments to find out which way to do the check. Somewhat delicate.
tc_hs_type (HsEqTy ty1 ty2) exp_kind 
  = do { (ty1', kind1) <- tc_infer_lhs_type ty1
       ; (ty2', kind2) <- tc_infer_lhs_type ty2
       ; let (tvs1, _) = splitForAllTysInvisible kind1
             (tvs2, _) = splitForAllTysInvisible kind2
       ; tys <-
         if length tvs1 > length tvs2
         then do { ty1'' <- checkExpectedKind ty1' kind1 kind2
                 ; return [ty1'', ty2'] }
         else do { ty2'' <- checkExpectedKind ty2' kind2 kind1
                 ; return [ty1', ty2''] }
       ; let ty' = mkNakedTyConApp eqTyCon (kind1 : tys)
       ; checkExpectedKind ty' constraintKind exp_kind }

--------- Literals
tc_hs_type (HsTyLit (HsNumTy n)) exp_kind
  = do { checkWiredInTyCon typeNatKindCon
       ; checkExpectedKind (mkNumLitTy n) typeNatKind exp_kind }

tc_hs_type (HsTyLit (HsStrTy s)) exp_kind
  = do { checkWiredInTyCon typeSymbolKindCon
       ; checkExpectedKind (mkStrLitTy s) typeSymbolKind exp_kind }

--------- Potentially kind-polymorphic types: call the "up" checker
-- See Note [Future-proofing the type checker]
tc_hs_type ty@(HsTyVar {})   ek = tc_infer_hs_type_ek ty ek
tc_hs_type ty@(HsAppTy {})   ek = tc_infer_hs_type_ek ty ek
tc_hs_type ty@(HsOpTy {})    ek = tc_infer_hs_type_ek ty ek
tc_hs_type ty@(HsKindSig {}) ek = tc_infer_hs_type_ek ty ek
tc_hs_type ty@(HsCoreTy {})  ek = tc_infer_hs_type_ek ty ek

tc_hs_type HsWildcardTy _ = panic "tc_hs_type HsWildcardTy"
-- unnamed wildcards should have been replaced by named wildcards

tc_hs_type (HsNamedWildcardTy name) exp_kind
  = do { (ty, k) <- tcTyVar name
       ; checkExpectedKind ty k exp_kind }

---------------------------
-- | Call 'tc_infer_hs_type' and check its result against an expected kind.
tc_infer_hs_type_ek :: HsType Name -> TcKind -> TcM TcType
tc_infer_hs_type_ek ty ek
  = do { (ty', k) <- tc_infer_hs_type ty
       ; checkExpectedKind ty' k ek }

---------------------------
tupKindSort_maybe :: TcKind -> Maybe TupleSort
tupKindSort_maybe k
  | isConstraintKind k = Just ConstraintTuple
  | isLiftedTypeKind k = Just BoxedTuple
  | otherwise          = Nothing

tc_tuple :: TupleSort -> [LHsType Name] -> TcKind -> TcM TcType
tc_tuple tup_sort tys exp_kind
  = do { arg_kinds <- case tup_sort of
           BoxedTuple      -> return (nOfThem arity liftedTypeKind)
           UnboxedTuple    -> do { levs <- newFlexiTyVarTys arity levityTy
                                 ; return $ map tYPE levs }
           ConstraintTuple -> return (nOfThem arity constraintKind)
       ; tau_tys <- tcHsArgTys tys arg_kinds
       ; finish_tuple tup_sort tau_tys exp_kind }
  where
    arity   = length tys

finish_tuple :: TupleSort -> [TcType] -> TcKind -> TcM TcType
finish_tuple tup_sort tau_tys exp_kind
  = do { traceTc "finish_tuple" (ppr res_kind $$ ppr exp_kind $$ ppr exp_kind)
       ; tau_tys' <- zonkTcTypes tau_tys  -- necessary so that the getLevity works
       ; let arg_tys  = case tup_sort of
                   -- See also Note [Unboxed tuple levity vars] in TyCon
                 UnboxedTuple    -> map (getLevity "finish_tuple") tau_tys' ++ tau_tys'
                 BoxedTuple      -> tau_tys
                 ConstraintTuple -> tau_tys
       ; checkWiredInTyCon tycon
       ; checkExpectedKind (mkTyConApp tycon arg_tys) res_kind exp_kind }
  where
    tycon = tupleTyCon tup_sort (length tau_tys)
    res_kind = case tup_sort of
                 UnboxedTuple    -> unliftedTypeKind
                 BoxedTuple      -> liftedTypeKind
                 ConstraintTuple -> constraintKind

---------------------------
tcInferApps :: Outputable a
       => a 
       -> TcKind                        -- Function kind (zonked)
       -> [LHsType Name]                -- Arg types
       -> TcM ([TcType], TcKind)        -- Kind-checked args
tcInferApps the_fun = go
  where
    the_fun_doc = ppr the_fun
    
    go fun_kind [] = return ([], fun_kind)
    go fun_kind (arg:args)
      | Just (bndr, res_k) <- splitForAllTy_maybe fun_kind
      , isInvisibleBinder bndr
      , Just tv <- binderVar_maybe bndr
      = do { imp_param <- newFlexiTyVarTy (tyVarKind tv)
           ; (args', res_kind) <-
                go (substTyWith [tv] [imp_param] res_k) (arg:args)
           ; return (imp_param : args', res_kind) }

      | Just (bndr, res_k) <- splitForAllTy_maybe fun_kind
      , Just tv <- binderVar_maybe bndr
      , isVisibleBinder bndr
      = do { arg' <- tc_lhs_type arg (tyVarKind tv)
           ; (args', res_kind) <-
               go (substTyWith [tv] [arg'] res_k) args
           ; return (arg' : args', res_kind) }

      | Just (arg_k, res_k) <- splitFunTy_maybe fun_kind
      = do { arg' <- tc_lhs_type arg arg_k
           ; (args', res_kind) <- go res_k args
           ; return (arg' : args', res_kind) }

      | otherwise   -- we hopefully just have a flexi. unify with (k1 -> k2)
      = do { mb_k <- matchExpectedFunKind fun_kind
           ; case mb_k of
               Just k  -> go k (arg:args)
               Nothing -> failWithTc too_many_args }

    too_many_args = quotes the_fun_doc <+>
                    ptext (sLit "is applied to too many type arguments")


---------------------------
tcHsContext :: LHsContext Name -> TcM [PredType]
tcHsContext ctxt = mapM tcHsLPredType (unLoc ctxt)

tcHsLPredType :: LHsType Name -> TcM PredType
tcHsLPredType pred = tc_lhs_type pred constraintKind

---------------------------
tcTyVar :: Name -> TcM (TcType, TcKind)
-- See Note [Type checking recursive type and class declarations]
-- in TcTyClsDecls
tcTyVar name         -- Could be a tyvar, a tycon, or a datacon
  = do { traceTc "lk1" (ppr name)
       ; thing <- tcLookup name
       ; case thing of
           ATyVar _ tv -> return (mkTyCoVarTy tv, tyVarKind tv)

           AThing kind -> do { tc <- get_loopy_tc name
                             ; return (mkNakedTyConApp tc [], kind) }
                             -- mkNakedTyConApp: see Note [Zonking inside the knot]

           AGlobal (ATyCon tc) -> return (mkTyConApp tc [], tyConKind tc)

           AGlobal (AConLike (RealDataCon dc))
             -> do { data_kinds <- xoptM Opt_DataKinds
                   ; unless data_kinds $ promotionErr name NoDataKinds
                   ; let tc = promoteDataCon dc
                   ; return (mkNakedTyConApp tc [], tyConKind tc) }

           APromotionErr err -> promotionErr name err

           _  -> wrongThingErr "type" thing name }
  where
    get_loopy_tc name
      = do { env <- getGblEnv
           ; case lookupNameEnv (tcg_type_env env) name of
                Just (ATyCon tc) -> return tc
                _                -> return (aThingErr "tcTyVar" name) }

tcClass :: Name -> TcM (Class, TcKind)
tcClass cls     -- Must be a class
  = do { thing <- tcLookup cls
       ; case thing of
           AThing kind -> return (aThingErr "tcClass" cls, kind)
           AGlobal (ATyCon tc)
             | Just cls <- tyConClass_maybe tc 
             -> return (cls, tyConKind tc)
           _ -> wrongThingErr "class" thing cls }


aThingErr :: String -> Name -> b
-- The type checker for types is sometimes called simply to
-- do *kind* checking; and in that case it ignores the type
-- returned. Which is a good thing since it may not be available yet!
aThingErr str x = pprPanic "AThing evaluated unexpectedly" (text str <+> ppr x)

{-
Note [Zonking inside the knot]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we are checking the argument types of a data constructor.  We
must zonk the types before making the DataCon, because once built we
can't change it.  So we must traverse the type.

BUT the parent TyCon is knot-tied, so we can't look at it yet. 

So we must be careful not to use "smart constructors" for types that
look at the TyCon or Class involved.  

  * Hence the use of mkNakedXXX functions. These do *not* enforce 
    the invariants (for example that we use (ForAllTy (Anon s) t) rather 
    than (TyConApp (->) [s,t])).  

  * Ditto in zonkTcType (which may be applied more than once, eg to
    squeeze out kind meta-variables), we are careful not to look at
    the TyCon.

  * We arrange to call zonkSigType *once* right at the end, and it
    does establish the invariants.  But in exchange we can't look
    at the result (not even its structure) until we have emerged
    from the "knot".

  * TcHsSyn.zonkTcTypeToType also can safely check/establish
    invariants.

This is horribly delicate.  I hate it.  A good example of how
delicate it is can be seen in Trac #7903.
-}

zonkSigType :: TcType -> TcM TcType
-- Zonk the result of type-checking a user-written type signature
-- It may have kind variables in it, but no meta type variables
-- Because of knot-typing (see Note [Zonking inside the knot])
-- it may need to establish the Type invariants;
-- hence the use of mkTyConApp and mkAppTy
zonkSigType ty
  = go ty
  where
    go (TyConApp tc tys) = do tys' <- mapM go tys
                              return (mkTyConApp tc tys')
                -- Key point: establish Type invariants!
                -- See Note [Zonking inside the knot]

    go (LitTy n)         = return (LitTy n)

    go (ForAllTy (Anon arg) res)
                         = do arg' <- go arg
                              res' <- go res
                              return (mkFunTy arg' res')

    go (AppTy fun arg)   = do fun' <- go fun
                              arg' <- go arg
                              return (mkAppTy fun' arg')
                -- NB the mkAppTy; we might have instantiated a
                -- type variable to a type constructor, so we need
                -- to pull the TyConApp to the top.

        -- The two interesting cases!
    go (TyVarTy tyvar) | isTcTyVar tyvar = zonkTcTyCoVar tyvar
                       | otherwise       = TyVarTy <$> updateTyVarKindM go tyvar
                -- Ordinary (non Tc) tyvars occur inside quantified types

    go (ForAllTy (Named tv vis) ty)
                            = do { tv' <- zonkTcTyCoVarBndr tv
                                 ; ty' <- go ty
                                 ; return (mkNamedForAllTy tv' vis ty') }

    go (CastTy ty co) = do { ty' <- go ty
                           ; co' <- zonkCoToCo emptyZonkEnv co  -- TODO (RAE): This is wrong.
                           ; return (CastTy ty' co') }
    go (CoercionTy co) = CoercionTy <$> zonkCoToCo emptyZonkEnv co -- TODO (RAE): Still wrong.

{-
Note [Body kind of a forall]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The body of a forall is usually a type, but in principle
there's no reason to prohibit *unlifted* types.
In fact, GHC can itself construct a function with an
unboxed tuple inside a for-all (via CPR analyis; see 
typecheck/should_compile/tc170).

Moreover in instance heads we get forall-types with
kind Constraint.  

Moreover if we have a signature
   f :: Int#
then we represent it as (HsForAll Implicit [] [] Int#).  And this must
be legal!  We can't drop the empty forall until *after* typechecking
the body because of kind polymorphism:
   Typeable :: forall k. k -> Constraint
   data Apply f t = Apply (f t)
   -- Apply :: forall k. (k -> *) -> k -> *
   instance Typeable Apply where ...
Then the dfun has type
   df :: forall k. Typeable ((k->*) -> k -> *) (Apply k)

   f :: Typeable Apply

   f :: forall (t:k->*) (a:k).  t a -> t a

   class C a b where
      op :: a b -> Typeable Apply

   data T a = MkT (Typeable Apply)
            | T2 a
      T :: * -> *
      MkT :: forall k. (Typeable ((k->*) -> k -> *) (Apply k)) -> T a

   f :: (forall (k:*). forall (t:: k->*) (a:k). t a -> t a) -> Int
   f :: (forall a. a -> Typeable Apply) -> Int

So we *must* keep the HsForAll on the instance type
   HsForAll Implicit [] [] (Typeable Apply)
so that we do kind generalisation on it.

Really we should check that it's a type of value kind
{*, Constraint, #}, but I'm not doing that yet
Example that should be rejected:  
         f :: (forall (a:*->*). a) Int

Note [Inferring tuple kinds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Give a tuple type (a,b,c), which the parser labels as HsBoxedOrConstraintTuple,
we try to figure out whether it's a tuple of kind * or Constraint.
  Step 1: look at the expected kind
  Step 2: infer argument kinds

If after Step 2 it's not clear from the arguments that it's
Constraint, then it must be *.  Once having decided that we re-check
the Check the arguments again to give good error messages
in eg. `(Maybe, Maybe)`

Note that we will still fail to infer the correct kind in this case:

  type T a = ((a,a), D a)
  type family D :: Constraint -> Constraint

While kind checking T, we do not yet know the kind of D, so we will default the
kind of T to * -> *. It works if we annotate `a` with kind `Constraint`.

Note [Desugaring types]
~~~~~~~~~~~~~~~~~~~~~~~
The type desugarer is phase 2 of dealing with HsTypes.  Specifically:

  * It transforms from HsType to Type

  * It zonks any kinds.  The returned type should have no mutable kind
    or type variables (hence returning Type not TcType):
      - any unconstrained kind variables are defaulted to (Any *) just 
        as in TcHsSyn. 
      - there are no mutable type variables because we are 
        kind-checking a type
    Reason: the returned type may be put in a TyCon or DataCon where
    it will never subsequently be zonked.

You might worry about nested scopes:
        ..a:kappa in scope..
            let f :: forall b. T '[a,b] -> Int
In this case, f's type could have a mutable kind variable kappa in it;
and we might then default it to (Any *) when dealing with f's type
signature.  But we don't expect this to happen because we can't get a
lexically scoped type variable with a mutable kind variable in it.  A
delicate point, this.  If it becomes an issue we might need to
distinguish top-level from nested uses.

Moreover
  * it cannot fail, 
  * it does no unifications
  * it does no validity checking, except for structural matters, such as
        (a) spurious ! annotations.
        (b) a class used as a type

Note [Kind of a type splice]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider these terms, each with TH type splice inside:
     [| e1 :: Maybe $(..blah..) |]
     [| e2 :: $(..blah..) |]
When kind-checking the type signature, we'll kind-check the splice
$(..blah..); we want to give it a kind that can fit in any context,
as if $(..blah..) :: forall k. k.  

In the e1 example, the context of the splice fixes kappa to *.  But
in the e2 example, we'll desugar the type, zonking the kind unification
variables as we go.  When we encounter the unconstrained kappa, we
want to default it to '*', not to (Any *).


Help functions for type applications
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-}

addTypeCtxt :: LHsType Name -> TcM a -> TcM a
        -- Wrap a context around only if we want to show that contexts.  
        -- Omit invisble ones and ones user's won't grok
addTypeCtxt (L _ ty) thing 
  = addErrCtxt doc thing
  where
    doc = ptext (sLit "In the type") <+> quotes (ppr ty)

{-
************************************************************************
*                                                                      *
                Type-variable binders
%*                                                                      *
%************************************************************************
-}

-- | Kind-check a 'LHsTyVarBndrs'. If the decl under consideration has a complete,
-- user-supplied kind signature (CUSK), generalise the result. Used in 'getInitialKind'
-- and in kind-checking. See also Note [Complete user-supplied kind signatures] in
-- HsDecls.
kcHsTyVarBndrs :: Bool    -- ^ True <=> the decl being checked has a CUSK
               -> LHsTyVarBndrs Name 
               -> TcM (Kind, r)   -- ^ the result kind, possibly with other info
               -> TcM (Kind, r)   -- ^ The full kind of the thing being declared,
                                  -- with the other info
kcHsTyVarBndrs cusk (HsQTvs { hsq_implicit = kv_ns, hsq_explicit = hs_tvs }) thing_inside
  = do { meta_kvs <- mapM (const newMetaKindVar) kv_ns
       ; kvs <- if cusk
                then return $ zipWith new_skolem_tv kv_ns meta_kvs
                     -- the names must line up in splitTelescopeTvs
                else zipWithM newSigTyVar kv_ns meta_kvs
       ; tcExtendTyVarEnv2 (kv_ns `zip` kvs) $
    do { (full_kind, _, stuff) <- bind_telescope hs_tvs thing_inside
       ; let _all_kvs  = filter (not . isMetaTyVar) $
                         varSetElems $ tyCoVarsOfType full_kind

                -- the free non-meta variables in the returned kind should be
                -- exactly the same set of variables we list as implicit kind vars
                -- BUT, it is critical that we generalise w.r.t. the declared kvs,
                -- not the found _all_kvs, because we depend hsq_implicit and the
                -- quantified tyvars to line up in kcTyClTyVars
             gen_kind  = if cusk
                         then ASSERT( sort _all_kvs == sort kvs ) 
                              mkInvForAllTys kvs full_kind
                         else full_kind
       ; return (gen_kind, stuff) } }
  where
      -- there may be dependency between the explicit "ty" vars. So, we have
      -- to handle them one at a time. We also need to build up a full kind
      -- here, because this is the place we know whether to use a FunTy or a
      -- ForAllTy. We prefer using an anonymous binder over a trivial named
      -- binder. If a user wants a trivial named one, use an explicit kind
      -- signature.
    bind_telescope :: [LHsTyVarBndr Name] -> TcM (Kind, r) -> TcM (Kind, VarSet, r)
    bind_telescope [] thing
      = do { (res_kind, stuff) <- thing
           ; return (res_kind, tyCoVarsOfType res_kind, stuff) }
    bind_telescope (L _ hs_tv : hs_tvs) thing
      = do { (n,k) <- kc_hs_tv hs_tv
           ; (res_kind, fvs, stuff) <- tcExtendTyVarEnv2 [(n,new_skolem_tv n k)] $ bind_telescope hs_tvs thing
              -- we must be *lazy* in res_kind and fvs (assuming that the
              -- caller of kcHsTyVarBndrs is, too), as sometimes these hold
              -- panics. See kcConDecl.
           ; let m_kv = lookupVarSetByName fvs n
                 (bndr, fvs') = case m_kv of
                   Just kv -> ( mkNamedBinder kv Visible
                              , fvs `delVarSet` kv
                                    `unionVarSet` tyCoVarsOfType k )
                   Nothing -> ( mkAnonBinder k
                              , fvs `unionVarSet` tyCoVarsOfType k )

           ; return ( mkForAllTy bndr res_kind, fvs', stuff ) }

    kc_hs_tv :: HsTyVarBndr Name -> TcM (Name, TcKind)
    kc_hs_tv (UserTyVar n)
      = do { mb_thing <- tcLookupLcl_maybe n
           ; kind <- case mb_thing of
                       Just (AThing k) -> return k
                       _ | cusk        -> return liftedTypeKind
                         | otherwise   -> newMetaKindVar
           ; return (n, kind) }
    kc_hs_tv (KindedTyVar n k) 
      = do { kind <- tcLHsKind k
               -- In an associated type decl, the type variable may already 
               -- be in scope; in that case we want to make sure its kind
               -- matches the one declared here
           ; mb_thing <- tcLookupLcl_maybe n
           ; case mb_thing of
               Nothing          -> return ()
                                     -- we only need the side effects;
                                     -- no need for coercion
               Just (AThing ks) -> unifyType_ kind ks
               Just thing       -> pprPanic "check_in_scope" (ppr thing)
           ; return (n, kind) }

tcHsTyVarBndrs :: LHsTyVarBndrs Name 
               -> ([TcTyVar] -> TcM r)
               -> TcM r
-- Bind the kind variables to fresh skolem variables
-- and type variables to skolems, each with a meta-kind variable kind
tcHsTyVarBndrs (HsQTvs { hsq_implicit = kv_ns, hsq_explicit = hs_tvs }) thing_inside
  = go (map UserTyVar kv_ns ++ map unLoc hs_tvs) $ \tvs ->
    do { traceTc "tcHsTyVarBndrs {" (vcat [ text "Hs implicit vars:" <+> ppr kv_ns
                                          , text "Hs explicit vars:" <+> ppr hs_tvs
                                          , text "Tyvars:" <+> ppr tvs ])
       ; result <- thing_inside tvs
       ; traceTc "tcHsTyVarBndrs }" (vcat [ text "Hs implicit vars:" <+> ppr kv_ns
                                          , text "Hs explicit vars:" <+> ppr hs_tvs
                                          , text "Tyvars:" <+> ppr tvs ])
       ; return result }
  where go [] thing = thing []
        go (hs_tv : hs_tvs) thing
          = tcHsTyVarBndr hs_tv $ \tv ->
            tcExtendTyVarEnv [tv] $
            go hs_tvs $ \tvs ->
            thing (tv : tvs)

tcHsTyVarBndr :: HsTyVarBndr Name -> (TcTyVar -> TcM r) -> TcM r
-- Bind a new type variable for thing_inside. This type variable
-- is given a meta-kind variable (for UserTyVar) or the type-checked kind
-- (for KindedTyVar)
--
-- If the variable is already in scope, use that one, instead of introducing a new
-- one. This can occur in 
--   instance C (a,b) where
--     type F (a,b) c = ...
-- Here a,b will be in scope when processing the associated type instance for F.
-- See Note [Associated type tyvar names] in Class
tcHsTyVarBndr hs_tv thing_inside
  = do { let name = hsTyVarName hs_tv
       ; mb_tv <- tcLookupLcl_maybe name
       ; case mb_tv of {
           Just (ATyVar _ tv) -> thing_inside tv ;
           _ -> do
       { kind <- case hs_tv of
                   UserTyVar {}       -> newMetaKindVar
                   KindedTyVar _ kind -> tcLHsKind kind
       ; thing_inside $ new_skolem_tv name kind } } }

-- makes a new skolem tv
new_skolem_tv :: Name -> Kind -> TcTyVar
new_skolem_tv n k = mkTcTyVar n k vanillaSkolemTv

------------------
kindGeneralize :: TyVarSet -> TcM [KindVar]
kindGeneralize tkvs
  = do { gbl_tvs <- tcGetGlobalTyVars -- Already zonked
       ; quantifyTyCoVars' gbl_tvs tkvs True }

{-
Note [Kind generalisation]
~~~~~~~~~~~~~~~~~~~~~~~~~~
We do kind generalisation only at the outer level of a type signature.
For example, consider
  T :: forall k. k -> *
  f :: (forall a. T a -> Int) -> Int
When kind-checking f's type signature we generalise the kind at
the outermost level, thus:
  f1 :: forall k. (forall (a:k). T k a -> Int) -> Int  -- YES!
and *not* at the inner forall:
  f2 :: (forall k. forall (a:k). T k a -> Int) -> Int  -- NO!
Reason: same as for HM inference on value level declarations,
we want to infer the most general type.  The f2 type signature
would be *less applicable* than f1, because it requires a more
polymorphic argument.

Note [Kinds of quantified type variables]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
tcTyVarBndrsGen quantifies over a specified list of type variables,
*and* over the kind variables mentioned in the kinds of those tyvars.

Note that we must zonk those kinds (obviously) but less obviously, we
must return type variables whose kinds are zonked too. Example
    (a :: k7)  where  k7 := k9 -> k9
We must return
    [k9, a:k9->k9]
and NOT 
    [k9, a:k7]
Reason: we're going to turn this into a for-all type, 
   forall k9. forall (a:k7). blah
which the type checker will then instantiate, and instantiate does not
look through unification variables!  

Hence using zonked_kinds when forming tvs'.

Note [Typechecking telescopes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The functions kcTyClTyVars and tcTyClTyVars have to bind the scoped type and kind
variables in a telescope. For example:

class Foo k (t :: Proxy k -> k2) where ...

By the time [kt]cTyClTyVars is called, we know *something* about the kind of Foo,
at least that it has the form

  Foo :: forall (k2 :: mk2). forall (k :: mk1). (Proxy mk1 k -> k2) -> Constraint

if it has a CUSK (Foo does not, in point of fact) or

  Foo :: forall (k :: mk1). (Proxy mk1 k -> k2) -> Constraint

if it does not, where mk1 and mk2 are meta-kind variables (mk1, mk2 :: *). 

When calling tcTyClTyVars, this kind is further generalized w.r.t. any
free variables appearing in mk1 or mk2. So, mk_telescope_tvs must handle
that possibility. Perhaps we discover that mk1 := Maybe k3 and mk2 := *,
so we have

Foo :: forall (k3 :: *). forall (k2 :: *). forall (k :: Maybe k3).
       (Proxy (Maybe k3) k -> k2) -> Constraint

We now have several sorts of variables to think about:
1) The variable k3 is not mentioned in the source at all. It is neither
   explicitly bound nor ever used. It is *not* a scoped kind variable,
   and should not be bound when type-checking the scope of the telescope.

2) The variable k2 is mentioned in the source, but it is not explicitly
   bound. It *is* a scoped kind variable, and will appear in the
   hsq_implicit field of a LHsTyVarBndrs.

3) The variable k is mentioned in the source with an explicit binding.
   It *is* a scoped type variable, and will appear in the
   hsq_explicit field of a LHsTyVarBndrs.

4) The variable t is bound in the source, but it is never mentioned later
   in the kind. It *is* a scoped variable (it can appear in the telescope
   scope, even though it is non-dependent), and will appear in the
   hsq_explicit field of a LHsTyVarBndrs.

splitTelescopeTvs walks through the output of a splitForAllTys on the
telescope head's kind (Foo, in our example), creating a list of tyvars
to be bound within the telescope scope. It must simultaneously walk
through the hsq_implicit and hsq_explicit fields of a LHsTyVarBndrs.
Comments in the code refer back to the cases in this Note.

Because all instances of case (1) come before all others, and
then all instances of case (2) come before all others, (the
implicitly bound vars always precede the explicitly bound ones), we
handle the lists in three stages (mk_tvs, mk_tvs1, and mk_tvs2).

Note [scopeTelescopeTvs Arity]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Now that type variables can have dependencies on other type variables,
it is impossible to figure how to line up an LHsTyVarBndrs with the binders
of a tycon's kind. The only way we can do so is by knowing how many binders
we're expecting. Then, we can drop the prefix of binders, which we're not
expecting (they're either undeclared kind variables or unmentioned kind
variables).

The only complication here is that, in the case of GADT-style data
definitions, the number of declared variables in LHsTyVarBndrs may be
too small, in case the user has given an explicit kind signature with
an arrow in it. Because this is a rare case, we take Maybe Arity in the
exported functions. If this is Nothing, we infer the arity from the
LHsTyVarBndrs. Otherwise, use the arity provided.
-}

--------------------
-- getInitialKind has made a suitably-shaped kind for the type or class
-- Unpack it, and attribute those kinds to the type variables
-- Extend the env with bindings for the tyvars, taken from
-- the kind of the tycon/class.  Give it to the thing inside, and 
-- check the result kind matches
kcLookupKind :: Name -> TcM Kind
kcLookupKind nm 
  = do { tc_ty_thing <- tcLookup nm
       ; case tc_ty_thing of
           AThing k            -> return k
           AGlobal (ATyCon tc) -> return (tyConKind tc)
           _                   -> pprPanic "kcLookupKind" (ppr tc_ty_thing) }

kcScopedKindVars :: [Name] -> TcM a -> TcM a
-- Given some tyvar binders like [a (b :: k -> *) (c :: k)]
-- bind each scoped kind variable (k in this case) to a fresh
-- kind skolem variable
kcScopedKindVars kv_ns thing_inside
  = do { kv_kinds <- mapM (const newMetaKindVar) kv_ns
       ; kvs <- zipWithM newSigTyVar kv_ns kv_kinds
                     -- NB: use mutable signature variables
       ; tcExtendTyVarEnv2 (kv_ns `zip` kvs) thing_inside }

-- See Note [Typechecking telescopes]
-- TODO (RAE): Update note!
scopeTelescopeTvs :: Kind         -- of the head of the telescope
                  -> Arity        -- See Note [scopeTelescopeTvs arity]
                  -> LHsTyVarBndrs Name
                  -> ([TyVar] -> Kind -> TcM a)
                        -- args are *quant'd* tyvars and the inner kind
                  -> TcM a
scopeTelescopeTvs kind n_declared
                  (HsQTvs { hsq_implicit = hs_kvs, hsq_explicit = hs_tvs })
                  thing_inside
  = do { let (bndrs, inner_ki) = splitForAllTys kind
             n_bndrs           = length bndrs
             (undeclared_bndrs, declared_bndrs)
                               = splitAt (n_bndrs - n_declared) bndrs
             undeclared_tyvars = map (expectJust "scopeTelescopeTvs" . 
                                      binderVar_maybe) undeclared_bndrs
             (declared_tyvars, extra_bndrs)
                               = zip_with_extra mk_tv declared_bndrs hs_tvs
       ; kcScopedKindVars hs_kvs $
         tcExtendTyVarEnv declared_tyvars $
         thing_inside (undeclared_tyvars ++ declared_tyvars)
                      (mkForAllTys extra_bndrs inner_ki) }
  where
    mk_tv :: Binder
          -> LHsTyVarBndr Name
          -> TyVar
    mk_tv bndr hs_tv
      | Just tv <- binderVar_maybe bndr
      = tv
        
      | otherwise
      = mkTyVar (hsLTyVarName hs_tv) (binderType bndr)

    -- like zipWith, but also returns leftover elts from the first list
    zip_with_extra :: (a -> b -> c) -> [a] -> [b] -> ([c], [a])
    zip_with_extra f = go []
      where
        go acc (a:as) (b:bs) = go (f a b : acc) as bs
        go acc as     []     = (reverse acc, as)
        go _   _      _      = panic "zip_with_extra"

kcTyClTyVars :: Name -> LHsTyVarBndrs Name -> TcM () -> TcM ()
-- Used for the type variables of a type or class decl,
-- when doing the initial kind-check.  
kcTyClTyVars name hs_tvs thing_inside
  = do { let n_declared = length $ hsQTvExplicit hs_tvs
       ; tc_kind <- kcLookupKind name
       ; scopeTelescopeTvs tc_kind n_declared hs_tvs $ \ _all_tvs _ -> do
       { traceTc "kcTyClTyVars scopeTelescopeTvs:"
           (vcat [ text "Tycon:" <+> ppr name
                 , text "Kind:" <+> ppr tc_kind
                 , text "hs_tvs:" <+> ppr hs_tvs
                 , text "tvs:" <+> pprWithCommas pp_tv _all_tvs ])
       ; thing_inside }}
  where
    pp_tv tv = ppr tv <+> dcolon <+> ppr (tyVarKind tv)
      
-----------------------
tcTyClTyVars :: Name -> Maybe Arity  -- see Note [scopeTelescopeTvs Arity]
             -> LHsTyVarBndrs Name      -- LHS of the type or class decl
             -> ([TyVar] -> Kind -> Kind -> TcM a) -> TcM a
-- Used for the type variables of a type or class decl,
-- on the second pass when constructing the final result
-- (tcTyClTyVars T [a,b] thing_inside) 
--   where T : forall k1 k2 (a:k1 -> *) (b:k1). k2 -> *
--   calls thing_inside with arguments
--      [k1,k2,a,b] (forall (k1:*) (k2:*) (a:k1 -> *) (b:k1). k2 -> *) (k2 -> *)
--   having also extended the type environment with bindings 
--   for k1,k2,a,b
--
-- No need to freshen the k's because they are just skolem 
-- constants here, and we are at top level anyway.
tcTyClTyVars tycon m_n_declared hs_tvs thing_inside
  = do { let n_declared = m_n_declared `orElse` (length $ hsQTvExplicit hs_tvs)
       ; thing <- tcLookup tycon
       ; let kind = case thing of
                      AThing kind -> kind
                      _ -> panic "tcTyClTyVars"
                     -- We only call tcTyClTyVars during typechecking in
                     -- TcTyClDecls, where the local env is extended with
                     -- the generalized_env (mapping Names to AThings).
       ; scopeTelescopeTvs kind n_declared hs_tvs $ \ all_tvs res_k -> do
       { traceTc "tcTyClTyVars splitTelescopeTvs:"
           (vcat [ text "Tycon:" <+> ppr tycon
                 , text "Kind:" <+> ppr kind
                 , text "hs_tvs:" <+> ppr hs_tvs
                 , text "all tvs:" <+> pprWithCommas pp_tv all_tvs
                 , text "res_k:" <+> ppr res_k] )
       ; thing_inside all_tvs kind res_k }}
  where
    pp_tv tv = ppr tv <+> dcolon <+> ppr (tyVarKind tv)

-----------------------------------
tcDataKindSig :: Kind -> TcM [TyVar]
-- GADT decls can have a (perhaps partial) kind signature
--      e.g.  data T :: * -> * -> * where ...
-- This function makes up suitable (kinded) type variables for 
-- the argument kinds, and checks that the result kind is indeed *.
-- We use it also to make up argument type variables for for data instances.
tcDataKindSig kind
  = do  { checkTc (isLiftedTypeKind res_kind) (badKindSig kind)
        ; span <- getSrcSpanM
        ; us   <- newUniqueSupply 
        ; rdr_env <- getLocalRdrEnv
        ; let uniqs = uniqsFromSupply us
              occs  = [ occ | str <- allNameStrings
                            , let occ = mkOccName tvName str
                            , isNothing (lookupLocalRdrOcc rdr_env occ) ]
                 -- Note [Avoid name clashes for associated data types]

        ; return [ mk_tv span uniq occ kind 
                 | ((kind, occ), uniq) <- arg_kinds `zip` occs `zip` uniqs ] }
  where
    (arg_kinds, res_kind) = splitFunTys kind
    mk_tv loc uniq occ kind 
      = mkTyVar (mkInternalName uniq occ loc) kind
          
badKindSig :: Kind -> SDoc
badKindSig kind 
 = hang (ptext (sLit "Kind signature on data type declaration has non-* return kind"))
        2 (ppr kind)

{-
Note [Avoid name clashes for associated data types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider    class C a b where
               data D b :: * -> *
When typechecking the decl for D, we'll invent an extra type variable
for D, to fill out its kind.  Ideally we don't want this type variable
to be 'a', because when pretty printing we'll get
            class C a b where
               data D b a0 
(NB: the tidying happens in the conversion to IfaceSyn, which happens
as part of pretty-printing a TyThing.)

That's why we look in the LocalRdrEnv to see what's in scope. This is
important only to get nice-looking output when doing ":info C" in GHCi.
It isn't essential for correctness.


************************************************************************
*                                                                      *
                Scoped type variables
*                                                                      *
************************************************************************


tcAddScopedTyVars is used for scoped type variables added by pattern
type signatures
        e.g.  \ ((x::a), (y::a)) -> x+y
They never have explicit kinds (because this is source-code only)
They are mutable (because they can get bound to a more specific type).

Usually we kind-infer and expand type splices, and then
tupecheck/desugar the type.  That doesn't work well for scoped type
variables, because they scope left-right in patterns.  (e.g. in the
example above, the 'a' in (y::a) is bound by the 'a' in (x::a).

The current not-very-good plan is to
  * find all the types in the patterns
  * find their free tyvars
  * do kind inference
  * bring the kinded type vars into scope
  * BUT throw away the kind-checked type
        (we'll kind-check it again when we type-check the pattern)

This is bad because throwing away the kind checked type throws away
its splices.  But too bad for now.  [July 03]

Historical note:
    We no longer specify that these type variables must be univerally 
    quantified (lots of email on the subject).  If you want to put that 
    back in, you need to
        a) Do a checkSigTyVars after thing_inside
        b) More insidiously, don't pass in expected_ty, else
           we unify with it too early and checkSigTyVars barfs
           Instead you have to pass in a fresh ty var, and unify
           it with expected_ty afterwards
-}

tcHsPatSigType :: UserTypeCtxt
               -> HsWithBndrs Name (LHsType Name) -- The type signature
               -> TcM ( Type                      -- The signature
                      , [(Name, TcTyVar)]     -- The new bit of type environment, binding
                                              -- the scoped type variables
                      , [(Name, TcTyVar)] )   -- The wildcards
-- Used for type-checking type signatures in
-- (a) patterns           e.g  f (x::Int) = e
-- (b) result signatures  e.g. g x :: Int = e
-- (c) RULE forall bndrs  e.g. forall (x::Int). f x = x

tcHsPatSigType ctxt (HsWB { hswb_cts = hs_ty, hswb_vars = sig_vars
                          , hswb_wcs = sig_wcs })
  = addErrCtxt (pprSigCtxt ctxt empty (ppr hs_ty)) $
    do  { vars <- mapM new_tv sig_vars
        ; nwc_tvs <- mapM newWildcardVarMetaKind sig_wcs
        ; let nwc_binds = sig_wcs `zip` nwc_tvs
              ktv_binds = (sig_vars `zip` vars)
        ; sig_ty <- tcExtendTyVarEnv2 (ktv_binds ++ nwc_binds) $
                    tcHsLiftedType hs_ty
        ; sig_ty <- zonkSigType sig_ty
        ; checkValidType ctxt sig_ty
        ; emitWildcardHoleConstraints (zip sig_wcs nwc_tvs)
        ; return (sig_ty, ktv_binds, nwc_binds) }
  where
    new_tv name = do { kind <- newMetaKindVar
                     ; new_tkv name kind }

    new_tkv name kind  -- See Note [Pattern signature binders]
      = case ctxt of
          RuleSigCtxt {} -> return $ new_skolem_tv name kind
          _              -> newSigTyVar name kind -- See Note [Unifying SigTvs]

tcPatSig :: Bool                    -- True <=> pattern binding
         -> HsWithBndrs Name (LHsType Name)
         -> TcSigmaType
         -> TcM (TcType,            -- The type to use for "inside" the signature
                 [(Name, TcTyVar)], -- The new bit of type environment, binding
                                    -- the scoped type variables
                 [(Name, TcTyVar)], -- The wildcards
                 HsWrapper)         -- Coercion due to unification with actual ty
                                    -- Of shape:  res_ty ~ sig_ty
tcPatSig in_pat_bind sig res_ty
  = do  { (sig_ty, sig_tvs, sig_nwcs) <- tcHsPatSigType PatSigCtxt sig
        -- sig_tvs are the type variables free in 'sig',
        -- and not already in scope. These are the ones
        -- that should be brought into scope

        ; if null sig_tvs then do {
                -- Just do the subsumption check and return
                  wrap <- addErrCtxtM (mk_msg sig_ty) $
                          tcSubType_NC PatSigCtxt res_ty sig_ty
                ; return (sig_ty, [], sig_nwcs, wrap)
        } else do
                -- Type signature binds at least one scoped type variable
        
                -- A pattern binding cannot bind scoped type variables
                -- It is more convenient to make the test here
                -- than in the renamer
        { when in_pat_bind (addErr (patBindSigErr sig_tvs))

                -- Check that all newly-in-scope tyvars are in fact
                -- constrained by the pattern.  This catches tiresome
                -- cases like   
                --      type T a = Int
                --      f :: Int -> Int
                --      f (x :: T a) = ...
                -- Here 'a' doesn't get a binding.  Sigh
        ; let bad_tvs = [ tv | (_, tv) <- sig_tvs
                             , not (tv `elemVarSet` exactTyCoVarsOfType sig_ty) ]
        ; checkTc (null bad_tvs) (badPatSigTvs sig_ty bad_tvs)

        -- Now do a subsumption check of the pattern signature against res_ty
        ; wrap <- addErrCtxtM (mk_msg sig_ty) $
                  tcSubType_NC PatSigCtxt res_ty sig_ty

        -- Phew!
        ; return (sig_ty, sig_tvs, sig_nwcs, wrap)
        } }
  where
    mk_msg sig_ty tidy_env
       = do { (tidy_env, sig_ty) <- zonkTidyTcType tidy_env sig_ty
            ; (tidy_env, res_ty) <- zonkTidyTcType tidy_env res_ty
            ; let msg = vcat [ hang (ptext (sLit "When checking that the pattern signature:"))
                                  4 (ppr sig_ty)
                             , nest 2 (hang (ptext (sLit "fits the type of its context:"))
                                          2 (ppr res_ty)) ]
            ; return (tidy_env, msg) }

patBindSigErr :: [(Name, TcTyVar)] -> SDoc
patBindSigErr sig_tvs 
  = hang (ptext (sLit "You cannot bind scoped type variable") <> plural sig_tvs
          <+> pprQuotedList (map fst sig_tvs))
       2 (ptext (sLit "in a pattern binding signature"))

{-
Note [Pattern signature binders]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider
   data T = forall a. T a (a->Int)
   f (T x (f :: a->Int) = blah)

Here 
 * The pattern (T p1 p2) creates a *skolem* type variable 'a_sk', 
   It must be a skolem so that that it retains its identity, and    
   TcErrors.getSkolemInfo can thereby find the binding site for the skolem.

 * The type signature pattern (f :: a->Int) binds "a" -> a_sig in the envt

 * Then unificaiton makes a_sig := a_sk

That's why we must make a_sig a MetaTv (albeit a SigTv), 
not a SkolemTv, so that it can unify to a_sk.

For RULE binders, though, things are a bit different (yuk).  
  RULE "foo" forall (x::a) (y::[a]).  f x y = ...
Here this really is the binding site of the type variable so we'd like
to use a skolem, so that we get a complaint if we unify two of them
together.

Note [Unifying SigTvs]
~~~~~~~~~~~~~~~~~~~~~~
ALAS we have no decent way of avoiding two SigTvs getting unified.  
Consider
  f (x::(a,b)) (y::c)) = [fst x, y]
Here we'd really like to complain that 'a' and 'c' are unified. But
for the reasons above we can't make a,b,c into skolems, so they
are just SigTvs that can unify.  And indeed, this would be ok,
  f x (y::c) = case x of
                 (x1 :: a1, True) -> [x,y]
                 (x1 :: a2, False) -> [x,y,y]
Here the type of x's first component is called 'a1' in one branch and
'a2' in the other.  We could try insisting on the same OccName, but
they definitely won't have the sane lexical Name. 

I think we could solve this by recording in a SigTv a list of all the
in-scope variables that it should not unify with, but it's fiddly.


************************************************************************
*                                                                      *
        Checking kinds
*                                                                      *
************************************************************************

-}

-- | Produce an 'TcKind' suitable for a checking a type that can be * or #.
ekOpen :: TcM TcKind
ekOpen = do { lev <- newFlexiTyVarTy levityTy
            ; return (tYPE lev) }

unifyKinds :: [(TcType, TcKind)] -> TcM ([TcType], TcKind)
unifyKinds act_kinds
  = do { kind <- newMetaKindVar
       ; let check (ty, act_kind) = checkExpectedKind ty act_kind kind
       ; tys' <- mapM check act_kinds
       ; return (tys', kind) }

{-
************************************************************************
*                                                                      *
        Sort checking kinds
*                                                                      *
************************************************************************

tcLHsKind converts a user-written kind to an internal, sort-checked kind.
It does sort checking and desugaring at the same time, in one single pass.
It fails when the kinds are not well-formed (eg. data A :: * Int).
-}

tcLHsKind :: LHsKind Name -> TcM Kind
tcLHsKind k = addErrCtxt (ptext (sLit "In the kind") <+> quotes (ppr k)) $
              tc_lhs_type k liftedTypeKind

-- TODO (RAE): Remove?
_dataKindsErr :: Name -> SDoc
_dataKindsErr name
  = hang (ptext (sLit "Illegal kind:") <+> quotes (ppr name))
       2 (ptext (sLit "Perhaps you intended to use DataKinds"))

promotionErr :: Name -> PromotionErr -> TcM a
promotionErr name err
  = failWithTc (hang (pprPECategory err <+> quotes (ppr name) <+> ptext (sLit "cannot be used here"))
                   2 (parens reason))
  where
    reason = case err of
               FamDataConPE -> ptext (sLit "it comes from a data family instance")
               NoDataKinds  -> ptext (sLit "Perhaps you intended to use DataKinds")
               _ -> ptext (sLit "it is defined and used in the same recursive group")

{-
************************************************************************
*                                                                      *
                Scoped type variables
*                                                                      *
************************************************************************
-}

badPatSigTvs :: TcType -> [TyVar] -> SDoc
badPatSigTvs sig_ty bad_tvs
  = vcat [ fsep [ptext (sLit "The type variable") <> plural bad_tvs, 
                 quotes (pprWithCommas ppr bad_tvs), 
                 ptext (sLit "should be bound by the pattern signature") <+> quotes (ppr sig_ty),
                 ptext (sLit "but are actually discarded by a type synonym") ]
         , ptext (sLit "To fix this, expand the type synonym") 
         , ptext (sLit "[Note: I hope to lift this restriction in due course]") ]

