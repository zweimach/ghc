{-# LANGUAGE CPP #-}

module SimplCont (
    -- * The continuation type
    SimplCont(..), DupFlag(..),
    isSimplified,
    contIsDupable, contResultType, contHoleType,
    contIsTrivial, contArgs, 
    countValArgs, countArgs,
    mkBoringStop, mkRhsStop, mkLazyArgStop,
    contIsRhsOrArg, contIsRhs,
    interestingCallContext, interestingArg,

    -- * ArgInfo
    ArgInfo(..), ArgSpec(..), mkArgInfo,
    addValArgTo, addCastTo, addTyArgTo,
    argInfoExpr, argInfoAppArgs, pushSimplifiedArgs,
    ) where

#include "HsVersions.h"

import SimplEnv
import CoreSyn
import PprCore
import CoreUtils
import CoreUnfold
import Id
import Demand
import Type     hiding( substTy )
import Coercion hiding( substCo, substTy )
import Util
import Outputable
import FastString
import Pair

{-
************************************************************************
*                                                                      *
                The SimplCont and DupFlag types
*                                                                      *
************************************************************************

A SimplCont allows the simplifier to traverse the expression in a
zipper-like fashion.  The SimplCont represents the rest of the expression,
"above" the point of interest.

You can also think of a SimplCont as an "evaluation context", using
that term in the way it is used for operational semantics. This is the
way I usually think of it, For example you'll often see a syntax for
evaluation context looking like
        C ::= []  |  C e   |  case C of alts  |  C `cast` co
That's the kind of thing we are doing here, and I use that syntax in
the comments.


Key points:
  * A SimplCont describes a *strict* context (just like
    evaluation contexts do).  E.g. Just [] is not a SimplCont

  * A SimplCont describes a context that *does not* bind
    any variables.  E.g. \x. [] is not a SimplCont
-}

data SimplCont
  = Stop                -- An empty context, or <hole>
        OutType         -- Type of the <hole>
        CallCtxt        -- Tells if there is something interesting about
                        --          the context, and hence the inliner
                        --          should be a bit keener (see interestingCallContext)
                        -- Specifically:
                        --     This is an argument of a function that has RULES
                        --     Inlining the call might allow the rule to fire
                        -- Never ValAppCxt (use ApplyToVal instead)
                        -- or CaseCtxt (use Select instead)

  | CastIt            -- <hole> `cast` co
        OutCoercion             -- The coercion simplified
                                -- Invariant: never an identity coercion
        SimplCont

  | ApplyToVal {        -- <hole> arg
        sc_dup  :: DupFlag,          -- See Note [DupFlag invariants]
        sc_arg  :: InExpr,           -- The argument,
        sc_env  :: StaticEnv,        --     and its static env
        sc_cont :: SimplCont }

  | ApplyToTy {         -- <hole> ty
        sc_arg_ty  :: OutType,     -- Argument type
        sc_hole_ty :: OutType,     -- Type of the function, presumably (forall a. blah)
                                   -- See Note [The hole type in ApplyToTy]
        sc_cont    :: SimplCont }

  | Select              -- case <hole> of alts
        DupFlag                 -- See Note [DupFlag invariants]
        InId [InAlt] StaticEnv  -- The case binder, alts type, alts, and subst-env
        SimplCont

  -- The two strict forms have no DupFlag, because we never duplicate them
  | StrictBind                  -- (\x* \xs. e) <hole>
        InId [InBndr]           -- let x* = <hole> in e
        InExpr StaticEnv        --      is a special case
        SimplCont

  | StrictArg           -- f e1 ..en <hole>
        ArgInfo         -- Specifies f, e1..en, Whether f has rules, etc
                        --     plus strictness flags for *further* args
        CallCtxt        -- Whether *this* argument position is interesting
        SimplCont

  | TickIt
        (Tickish Id)    -- Tick tickish <hole>
        SimplCont

data DupFlag = NoDup       -- Unsimplified, might be big
             | Simplified  -- Simplified
             | OkToDup     -- Simplified and small

isSimplified :: DupFlag -> Bool
isSimplified NoDup = False
isSimplified _     = True       -- Invariant: the subst-env is empty

perhapsSubstTy :: DupFlag -> StaticEnv -> Type -> Type
perhapsSubstTy dup env ty
  | isSimplified dup = ty
  | otherwise        = substTy env ty

{-
Note [DupFlag invariants]
~~~~~~~~~~~~~~~~~~~~~~~~~
In both (ApplyToVal dup _ env k)
   and  (Select dup _ _ env k)
the following invariants hold

  (a) if dup = OkToDup, then continuation k is also ok-to-dup
  (b) if dup = OkToDup or Simplified, the subst-env is empty
      (and and hence no need to re-simplify)
-}

instance Outputable DupFlag where
  ppr OkToDup    = ptext (sLit "ok")
  ppr NoDup      = ptext (sLit "nodup")
  ppr Simplified = ptext (sLit "simpl")

instance Outputable SimplCont where
  ppr (Stop ty interesting)           = ptext (sLit "Stop") <> brackets (ppr interesting) <+> ppr ty
  ppr (ApplyToTy  { sc_arg_ty = ty
                  , sc_cont = cont }) = (ptext (sLit "ApplyToTy") <+> pprParendType ty) $$ ppr cont
  ppr (ApplyToVal { sc_arg = arg
                  , sc_dup = dup
                  , sc_cont = cont }) = (ptext (sLit "ApplyToVal") <+> ppr dup <+> pprParendExpr arg)
                                        $$ ppr cont
  ppr (StrictBind b _ _ _ cont)       = (ptext (sLit "StrictBind") <+> ppr b) $$ ppr cont
  ppr (StrictArg ai _ cont)           = (ptext (sLit "StrictArg") <+> ppr (ai_fun ai)) $$ ppr cont
  ppr (Select dup bndr alts se cont)  = (ptext (sLit "Select") <+> ppr dup <+> ppr bndr) $$
                                        ifPprDebug (nest 2 $ vcat [ppr (seTvSubst se), ppr alts]) $$ ppr cont
  ppr (CastIt co cont  )              = (ptext (sLit "CastIt") <+> ppr co) $$ ppr cont
  ppr (TickIt t cont)                 = (ptext (sLit "TickIt") <+> ppr t) $$ ppr cont


{- Note [The hole type in ApplyToTy]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The sc_hole_ty field of ApplyToTy records the type of the "hole" in the
continuation.  It is absolutely necessary to compute contHoleType, but it is
not used for anything else (and hence may not be evaluated).

Why is it necessary for contHoleType?  Consider the continuation
     ApplyToType Int (Stop Int)
corresponding to
     (<hole> @Int) :: Int
What is the type of <hole>?  It could be (forall a. Int) or (forall a. a),
and there is no way to know which, so we must record it.

In a chain of applications  (f @t1 @t2 @t3) we'll lazily compute exprType
for (f @t1) and (f @t1 @t2), which is potentially non-linear; but it probably
doesn't matter because we'll never compute them all.

************************************************************************
*                                                                      *
                ArgInfo and ArgSpec
*                                                                      *
************************************************************************
-}

data ArgInfo
  = ArgInfo {
        ai_fun   :: OutId,      -- The function
        ai_args  :: [ArgSpec],  -- ...applied to these args (which are in *reverse* order)
        ai_type  :: OutType,    -- Type of (f a1 ... an)

        ai_rules :: [CoreRule], -- Rules for this function

        ai_encl :: Bool,        -- Flag saying whether this function
                                -- or an enclosing one has rules (recursively)
                                --      True => be keener to inline in all args

        ai_strs :: [Bool],      -- Strictness of remaining arguments
                                --   Usually infinite, but if it is finite it guarantees
                                --   that the function diverges after being given
                                --   that number of args
        ai_discs :: [Int]       -- Discounts for remaining arguments; non-zero => be keener to inline
                                --   Always infinite
    }

data ArgSpec
  = ValArg OutExpr                    -- Apply to this (coercion or value); c.f. ApplyToVal
  | TyArg { as_arg_ty  :: OutType     -- Apply to this type; c.f. ApplyToTy
          , as_hole_ty :: OutType }   -- Type of the function (presumably forall a. blah)
  | CastBy OutCoercion                -- Cast by this; c.f. CastIt

instance Outputable ArgSpec where
  ppr (ValArg e)                 = ptext (sLit "ValArg") <+> ppr e
  ppr (TyArg { as_arg_ty = ty }) = ptext (sLit "TyArg") <+> ppr ty
  ppr (CastBy c)                 = ptext (sLit "CastBy") <+> ppr c

addValArgTo :: ArgInfo -> OutExpr -> ArgInfo
addValArgTo ai arg = ai { ai_args = ValArg arg : ai_args ai
                        , ai_type = funResultTy (ai_type ai) }

addTyArgTo :: ArgInfo -> OutType -> ArgInfo
addTyArgTo ai arg_ty = ai { ai_args = arg_spec : ai_args ai
                          , ai_type = applyTy poly_fun_ty arg_ty }
  where
    poly_fun_ty = ai_type ai
    arg_spec    = TyArg { as_arg_ty = arg_ty, as_hole_ty = poly_fun_ty }

addCastTo :: ArgInfo -> OutCoercion -> ArgInfo
addCastTo ai co = ai { ai_args = CastBy co : ai_args ai
                     , ai_type = pSnd (coercionKind co) }

argInfoAppArgs :: [ArgSpec] -> [OutExpr]
argInfoAppArgs []                              = []
argInfoAppArgs (CastBy {}                : _)  = []  -- Stop at a cast
argInfoAppArgs (ValArg e                 : as) = e       : argInfoAppArgs as
argInfoAppArgs (TyArg { as_arg_ty = ty } : as) = Type ty : argInfoAppArgs as

pushSimplifiedArgs :: SimplEnv -> [ArgSpec] -> SimplCont -> SimplCont
pushSimplifiedArgs _env []           k = k
pushSimplifiedArgs env  (arg : args) k
  = case arg of
      TyArg { as_arg_ty = arg_ty, as_hole_ty = hole_ty }
               -> ApplyToTy  { sc_arg_ty = arg_ty, sc_hole_ty = hole_ty, sc_cont = rest }
      ValArg e -> ApplyToVal { sc_arg = e, sc_env = env, sc_dup = Simplified, sc_cont = rest }
      CastBy c -> CastIt c rest
  where
    rest = pushSimplifiedArgs env args k
           -- The env has an empty SubstEnv

argInfoExpr :: OutId -> [ArgSpec] -> OutExpr
-- NB: the [ArgSpec] is reversed so that the first arg
-- in the list is the last one in the application
argInfoExpr fun rev_args
  = go rev_args
  where
    go []                              = Var fun
    go (ValArg a                 : as) = go as `App` a
    go (TyArg { as_arg_ty = ty } : as) = go as `App` Type ty
    go (CastBy co                : as) = mkCast (go as) co


{-
************************************************************************
*                                                                      *
                Functions on SimplCont
*                                                                      *
************************************************************************
-}

mkBoringStop :: OutType -> SimplCont
mkBoringStop ty = Stop ty BoringCtxt

mkRhsStop :: OutType -> SimplCont       -- See Note [RHS of lets] in CoreUnfold
mkRhsStop ty = Stop ty RhsCtxt

mkLazyArgStop :: OutType -> CallCtxt -> SimplCont
mkLazyArgStop ty cci = Stop ty cci

-------------------
contIsRhsOrArg :: SimplCont -> Bool
contIsRhsOrArg (Stop {})       = True
contIsRhsOrArg (StrictBind {}) = True
contIsRhsOrArg (StrictArg {})  = True
contIsRhsOrArg _               = False

contIsRhs :: SimplCont -> Bool
contIsRhs (Stop _ RhsCtxt) = True
contIsRhs _                = False

-------------------
contIsDupable :: SimplCont -> Bool
contIsDupable (Stop {})                         = True
contIsDupable (ApplyToTy  { sc_cont = k })      = contIsDupable k
contIsDupable (ApplyToVal { sc_dup = OkToDup }) = True -- See Note [DupFlag invariants]
contIsDupable (Select   OkToDup _ _ _ _)        = True -- ...ditto...
contIsDupable (CastIt _ k)                      = contIsDupable k
contIsDupable _                                 = False

-------------------
contIsTrivial :: SimplCont -> Bool
contIsTrivial (Stop {})                                         = True
contIsTrivial (ApplyToTy { sc_cont = k })                       = contIsTrivial k
contIsTrivial (ApplyToVal { sc_arg = Coercion _, sc_cont = k }) = contIsTrivial k
contIsTrivial (CastIt _ k)                                      = contIsTrivial k
contIsTrivial _                                                 = False

-------------------
contResultType :: SimplCont -> OutType
contResultType (Stop ty _)                  = ty
contResultType (CastIt _ k)                 = contResultType k
contResultType (StrictBind _ _ _ _ k)       = contResultType k
contResultType (StrictArg _ _ k)            = contResultType k
contResultType (Select _ _ _ _ k)           = contResultType k
contResultType (ApplyToTy  { sc_cont = k }) = contResultType k
contResultType (ApplyToVal { sc_cont = k }) = contResultType k
contResultType (TickIt _ k)                 = contResultType k

contHoleType :: SimplCont -> OutType
contHoleType (Stop ty _)                      = ty
contHoleType (TickIt _ k)                     = contHoleType k
contHoleType (CastIt co _)                    = pFst (coercionKind co)
contHoleType (Select d b _ se _)              = perhapsSubstTy d se (idType b)
contHoleType (StrictBind b _ _ se _)          = substTy se (idType b)
contHoleType (StrictArg ai _ _)               = funArgTy (ai_type ai)
contHoleType (ApplyToTy  { sc_hole_ty = ty }) = ty  -- See Note [The hole type in ApplyToTy]
contHoleType (ApplyToVal { sc_arg = e, sc_env = se, sc_dup = dup, sc_cont = k })
  = mkFunTy (perhapsSubstTy dup se (exprType e))
            (contHoleType k)

-------------------
countValArgs :: SimplCont -> Int
-- Count value arguments excluding coercions
countValArgs (ApplyToVal { sc_arg = arg, sc_cont = cont })
  | Coercion {} <- arg = countValArgs cont
  | otherwise          = 1 + countValArgs cont
countValArgs _         = 0

countArgs :: SimplCont -> Int
-- Count all arguments, including types, coercions, and other values
countArgs (ApplyToTy  { sc_cont = cont }) = 1 + countArgs cont
countArgs (ApplyToVal { sc_cont = cont }) = 1 + countArgs cont
countArgs _                               = 0

contArgs :: SimplCont -> (Bool, [ArgSummary], SimplCont)
-- Summarises value args, discards type args and coercions
-- The returned continuation of the call is only used to
-- answer questions like "are you interesting?"
contArgs cont
  | lone cont = (True, [], cont)
  | otherwise = go [] cont
  where
    lone (ApplyToTy  {}) = False  -- See Note [Lone variables] in CoreUnfold
    lone (ApplyToVal {}) = False
    lone (CastIt {})     = False
    lone _               = True

    go args (ApplyToVal { sc_arg = arg, sc_env = se, sc_cont = k })
                                        = go (is_interesting arg se : args) k
    go args (ApplyToTy { sc_cont = k }) = go args k
    go args (CastIt _ k)                = go args k
    go args k                           = (False, reverse args, k)

    is_interesting arg se = interestingArg (substExpr (text "contArgs") se arg)
                   -- Do *not* use short-cutting substitution here
                   -- because we want to get as much IdInfo as possible

{-
Note [Interesting call context]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We want to avoid inlining an expression where there can't possibly be
any gain, such as in an argument position.  Hence, if the continuation
is interesting (eg. a case scrutinee, application etc.) then we
inline, otherwise we don't.

Previously some_benefit used to return True only if the variable was
applied to some value arguments.  This didn't work:

        let x = _coerce_ (T Int) Int (I# 3) in
        case _coerce_ Int (T Int) x of
                I# y -> ....

we want to inline x, but can't see that it's a constructor in a case
scrutinee position, and some_benefit is False.

Another example:

dMonadST = _/\_ t -> :Monad (g1 _@_ t, g2 _@_ t, g3 _@_ t)

....  case dMonadST _@_ x0 of (a,b,c) -> ....

we'd really like to inline dMonadST here, but we *don't* want to
inline if the case expression is just

        case x of y { DEFAULT -> ... }

since we can just eliminate this case instead (x is in WHNF).  Similar
applies when x is bound to a lambda expression.  Hence
contIsInteresting looks for case expressions with just a single
default case.
-}

interestingCallContext :: SimplCont -> CallCtxt
-- See Note [Interesting call context]
interestingCallContext cont
  = interesting cont
  where
    interesting (Select _ _bndr _ _ _) = CaseCtxt
    interesting (ApplyToVal {})        = ValAppCtxt
        -- Can happen if we have (f Int |> co) y
        -- If f has an INLINE prag we need to give it some
        -- motivation to inline. See Note [Cast then apply]
        -- in CoreUnfold
    interesting (StrictArg _ cci _)         = cci
    interesting (StrictBind {})             = BoringCtxt
    interesting (Stop _ cci)                = cci
    interesting (TickIt _ k)                = interesting k
    interesting (ApplyToTy { sc_cont = k }) = interesting k
    interesting (CastIt _ k)                = interesting k
        -- If this call is the arg of a strict function, the context
        -- is a bit interesting.  If we inline here, we may get useful
        -- evaluation information to avoid repeated evals: e.g.
        --      x + (y * z)
        -- Here the contIsInteresting makes the '*' keener to inline,
        -- which in turn exposes a constructor which makes the '+' inline.
        -- Assuming that +,* aren't small enough to inline regardless.
        --
        -- It's also very important to inline in a strict context for things
        -- like
        --              foldr k z (f x)
        -- Here, the context of (f x) is strict, and if f's unfolding is
        -- a build it's *great* to inline it here.  So we must ensure that
        -- the context for (f x) is not totally uninteresting.


-------------------
mkArgInfo :: Id
          -> [CoreRule] -- Rules for function
          -> Int        -- Number of value args
          -> SimplCont  -- Context of the call
          -> ArgInfo

mkArgInfo fun rules n_val_args call_cont
  | n_val_args < idArity fun            -- Note [Unsaturated functions]
  = ArgInfo { ai_fun = fun, ai_args = [], ai_type = fun_ty
            , ai_rules = rules, ai_encl = False
            , ai_strs = vanilla_stricts
            , ai_discs = vanilla_discounts }
  | otherwise
  = ArgInfo { ai_fun = fun, ai_args = [], ai_type = fun_ty
            , ai_rules = rules
            , ai_encl = interestingArgContext rules call_cont
            , ai_strs  = add_type_str fun_ty arg_stricts
            , ai_discs = arg_discounts }
  where
    fun_ty = idType fun

    vanilla_discounts, arg_discounts :: [Int]
    vanilla_discounts = repeat 0
    arg_discounts = case idUnfolding fun of
                        CoreUnfolding {uf_guidance = UnfIfGoodArgs {ug_args = discounts}}
                              -> discounts ++ vanilla_discounts
                        _     -> vanilla_discounts

    vanilla_stricts, arg_stricts :: [Bool]
    vanilla_stricts  = repeat False

    arg_stricts
      = case splitStrictSig (idStrictness fun) of
          (demands, result_info)
                | not (demands `lengthExceeds` n_val_args)
                ->      -- Enough args, use the strictness given.
                        -- For bottoming functions we used to pretend that the arg
                        -- is lazy, so that we don't treat the arg as an
                        -- interesting context.  This avoids substituting
                        -- top-level bindings for (say) strings into
                        -- calls to error.  But now we are more careful about
                        -- inlining lone variables, so its ok (see SimplUtils.analyseCont)
                   if isBotRes result_info then
                        map isStrictDmd demands         -- Finite => result is bottom
                   else
                        map isStrictDmd demands ++ vanilla_stricts
               | otherwise
               -> WARN( True, text "More demands than arity" <+> ppr fun <+> ppr (idArity fun)
                                <+> ppr n_val_args <+> ppr demands )
                   vanilla_stricts      -- Not enough args, or no strictness

    add_type_str :: Type -> [Bool] -> [Bool]
    -- If the function arg types are strict, record that in the 'strictness bits'
    -- No need to instantiate because unboxed types (which dominate the strict
    -- types) can't instantiate type variables.
    -- add_type_str is done repeatedly (for each call); might be better
    -- once-for-all in the function
    -- But beware primops/datacons with no strictness
    add_type_str _ [] = []
    add_type_str fun_ty strs            -- Look through foralls
        | Just (_, fun_ty') <- splitForAllTy_maybe fun_ty       -- Includes coercions
        = add_type_str fun_ty' strs
    add_type_str fun_ty (str:strs)      -- Add strict-type info
        | Just (arg_ty, fun_ty') <- splitFunTy_maybe fun_ty
        = (str || isStrictType arg_ty) : add_type_str fun_ty' strs
    add_type_str _ strs
        = strs

{- Note [Unsaturated functions]
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider (test eyeball/inline4)
        x = a:as
        y = f x
where f has arity 2.  Then we do not want to inline 'x', because
it'll just be floated out again.  Even if f has lots of discounts
on its first argument -- it must be saturated for these to kick in
-}

interestingArgContext :: [CoreRule] -> SimplCont -> Bool
-- If the argument has form (f x y), where x,y are boring,
-- and f is marked INLINE, then we don't want to inline f.
-- But if the context of the argument is
--      g (f x y)
-- where g has rules, then we *do* want to inline f, in case it
-- exposes a rule that might fire.  Similarly, if the context is
--      h (g (f x x))
-- where h has rules, then we do want to inline f; hence the
-- call_cont argument to interestingArgContext
--
-- The ai-rules flag makes this happen; if it's
-- set, the inliner gets just enough keener to inline f
-- regardless of how boring f's arguments are, if it's marked INLINE
--
-- The alternative would be to *always* inline an INLINE function,
-- regardless of how boring its context is; but that seems overkill
-- For example, it'd mean that wrapper functions were always inlined
--
-- The call_cont passed to interestingArgContext is the context of
-- the call itself, e.g. g <hole> in the example above
interestingArgContext rules call_cont
  = notNull rules || enclosing_fn_has_rules
  where
    enclosing_fn_has_rules = go call_cont

    go (Select {})         = False
    go (ApplyToVal {})     = False  -- Shouldn't really happen
    go (ApplyToTy  {})     = False  -- Ditto
    go (StrictArg _ cci _) = interesting cci
    go (StrictBind {})     = False      -- ??
    go (CastIt _ c)        = go c
    go (Stop _ cci)        = interesting cci
    go (TickIt _ c)        = go c

    interesting RuleArgCtxt = True
    interesting _           = False
