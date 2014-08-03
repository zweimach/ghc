%
% (c) The University of Glasgow 2006-2012
%

\begin{code}
{-# LANGUAGE CPP #-}
module Kind (
        -- * Main data type
        SuperKind, Kind, typeKind,

        -- Kinds
        anyKind, liftedTypeKind, unliftedTypeKind, constraintKind,
        mkArrowKind, mkArrowKinds,

        -- Kind constructors...
        anyKindTyCon, liftedTypeKindTyCon,
        unliftedTypeKindTyCon, constraintKindTyCon,

        -- Super Kinds
        superKind, superKindTyCon,

        pprKind, pprParendKind,

        -- ** Deconstructing Kinds
        kindAppResult, synTyConResKind,

        -- ** Predicates on Kinds
        isLiftedTypeKind, isUnliftedTypeKind,
        isConstraintKind,
        returnsTyCon, returnsSuperKind, returnsConstraintKind,
        isKind, isKindVar,
        isSuperKind, isSuperKindCon,
        isConstraintKindCon,
        isAnyKind, isAnyKindCon,
        okArrowArgKind, okArrowResultKind,

        classifiesTypeWithValues,
        isStarKind, isStarKindSynonymTyCon,
        isSortPolymorphic, isSortPolymorphic_maybe
       ) where

#include "HsVersions.h"

import {-# SOURCE #-} Type       ( typeKind, piResultTy, coreViewOneStarKind )

import TyCoRep
import TysPrim
import TyCon
import Var
import PrelNames
import Data.Maybe
\end{code}

%************************************************************************
%*                                                                      *
        Functions over Kinds
%*                                                                      *
%************************************************************************

Note [Kind Constraint and kind *]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The kind Constraint is the kind of classes and other type constraints.
The special thing about types of kind Constraint is that
 * They are displayed with double arrow:
     f :: Ord a => a -> a
 * They are implicitly instantiated at call sites; so the type inference
   engine inserts an extra argument of type (Ord a) at every call site
   to f.

However, once type inference is over, there is *no* distinction between
Constraint and *.  Indeed we can have coercions between the two. Consider
   class C a where
     op :: a -> a
For this single-method class we may generate a newtype, which in turn
generates an axiom witnessing
    Ord a ~ (a -> a)
so on the left we have Constraint, and on the right we have *.
See Trac #7451.

Bottom line: although '*' and 'Constraint' are distinct TyCons, with
distinct uniques, they are treated as equal at all times except
during type inference.

Note [SuperKind]
~~~~~~~~~~~~~~~~
Ostensibly, SuperKind is the kind of kinds. But, because we have *:*
in Core, we don't want to distinguish superKind from liftedTypeKind
after typechecking. So, we consider superKind to be a subkind of
liftedTypeKind (and constraintKind) when checking Core, but we consider
it to be distinct beforehand. Thus, tc... thinks superKind is separate,
but non-tc functions do not.

\begin{code}
kindAppResult :: Kind -> [Type] -> Kind
kindAppResult k []     = k
kindAppResult k (a:as) = kindAppResult (piResultTy k a) as

-- | Find the result 'Kind' of a type synonym,
-- after applying it to its 'arity' number of type variables
-- Actually this function works fine on data types too,
-- but they'd always return '*', so we never need to ask
synTyConResKind :: TyCon -> Kind
synTyConResKind tycon = kindAppResult (tyConKind tycon) (mkOnlyTyVarTys (tyConTyVars tycon))

isConstraintKind, isAnyKind :: Kind -> Bool

isConstraintKindCon, isAnyKindCon, isSuperKindCon :: TyCon -> Bool

isAnyKindCon          tc = tyConUnique tc == anyKindTyConKey
isConstraintKindCon   tc = tyConUnique tc == constraintKindTyConKey
isSuperKindCon        tc = tyConUnique tc == superKindTyConKey

isAnyKind (TyConApp tc _) = isAnyKindCon tc
isAnyKind _               = False

isConstraintKind (TyConApp tc _) = isConstraintKindCon tc
isConstraintKind _               = False

-- | Does the given type "end" in the given tycon? For example @k -> [a] -> *@
-- ends in @*@ and @Maybe a -> [a]@ ends in @[]@.
returnsTyCon :: TyCon -> Type -> Bool
returnsTyCon tc (ForAllTy _ ty)  = returnsTyCon tc ty
returnsTyCon tc (FunTy    _ ty)  = returnsTyCon tc ty
returnsTyCon tc (TyConApp tc' _) = tc == tc'
returnsTyCon _  _                = False

returnsSuperKind :: Kind -> Bool
returnsSuperKind = returnsTyCon superKindTyCon

returnsConstraintKind :: Kind -> Bool
returnsConstraintKind = returnsTyCon constraintKindTyCon

-- | Tests whether the given type looks like "TYPE v", where v is a variable.
isSortPolymorphic :: Kind -> Bool
isSortPolymorphic = isJust . isSortPolymorphic_maybe

-- | Retrieves a levity variable in the given kind, if the kind is of the
-- form "TYPE v".
isSortPolymorphic_maybe :: Kind -> Maybe TyVar
isSortPolymorphic_maybe (TyConApp tc [TyVarTy v])
  | tc `hasKey` tYPETyConKey
  = Just v
isSortPolymorphic_maybe _ = Nothing

--------------------------------------------
--            Kinding for arrow (->)
-- Says when a kind is acceptable on lhs or rhs of an arrow
--     arg -> res

okArrowArgKind, okArrowResultKind :: Kind -> Bool
okArrowArgKind = classifiesTypeWithValues
okArrowResultKind = classifiesTypeWithValues

-----------------------------------------
--              Subkinding
-- The tc variants are used during type-checking, where ConstraintKind
-- and SuperKind are distinct from all other kinds
-- After type-checking (in core), Constraint, SuperKind, and liftedTypeKind are
-- indistinguishable

-- | Does this classify a type allowed to have values? Responds True to things
-- like *, #, TYPE Lifted, TYPE v, Constraint.
classifiesTypeWithValues :: Kind -> Bool
-- ^ True of any sub-kind of OpenTypeKind
classifiesTypeWithValues t | Just t' <- coreViewOneStarKind t = classifiesTypeWithValues t'
classifiesTypeWithValues (TyConApp tc [_]) = tc `hasKey` tYPETyConKey
classifiesTypeWithValues _ = False

-- | Is this kind equivalent to *?
isStarKind :: Kind -> Bool
isStarKind k | Just k' <- coreViewOneStarKind k = isStarKind k'
isStarKind (TyConApp tc [TyConApp l []]) = tc `hasKey` tYPETyConKey
                                        && l `hasKey` liftedDataConKey
isStarKind _ = False
                              -- See Note [Kind Constraint and kind *]

-- | Is the tycon @Constraint@ or @BOX@?
isStarKindSynonymTyCon :: TyCon -> Bool
isStarKindSynonymTyCon tc = tc `hasKey` superKindTyConKey
                         || tc `hasKey` constraintKindTyConKey

-- | Is this a kind (i.e. a type-of-types)?
isKind :: Kind -> Bool
isKind k = isSuperKind kty || isLevityTy kty
  where kty = typeKind k

\end{code}
