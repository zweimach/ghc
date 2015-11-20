{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998


HsTypes: Abstract syntax: user-defined types
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-} -- Note [Pass sensitive types]
                                      -- in module PlaceHolder
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}

module HsTypes (
        HsType(..), LHsType, HsKind, LHsKind,
        HsTyVarBndr(..), LHsTyVarBndr,
        LHsTyVarBndrs(..),
        HsWithBndrs(..),
        HsTupleSort(..), HsExplicitFlag(..),
        HsContext, LHsContext,
        HsTyLit(..),
        HsIPName(..), hsIPNameFS,
        HsAppType(..), LHsAppType,

        LBangType, BangType,
        HsSrcBang(..), HsImplBang(..),
        SrcStrictness(..), SrcUnpackedness(..),
        getBangType, getBangStrictness,

        ConDeclField(..), LConDeclField, pprConDeclFields,

        FieldOcc(..), LFieldOcc, mkFieldOcc,
        AmbiguousFieldOcc(..), mkAmbiguousFieldOcc,
        rdrNameAmbiguousFieldOcc, selectorAmbiguousFieldOcc,
        unambiguousFieldOcc, ambiguousFieldOcc,

        HsWildCardInfo(..), mkAnonWildCardTy, mkNamedWildCardTy,
        wildCardName, sameWildCard, sameNamedWildCard,
        isAnonWildCard, isNamedWildCard,

        mkHsQTvs, hsQTvExplicit, isHsKindedTyVar, hsTvbAllKinded,
        mkExplicitHsForAllTy, mkImplicitHsForAllTy, mkQualifiedHsForAllTy,
        mkHsForAllTy,
        flattenTopLevelLHsForAllTy,flattenTopLevelHsForAllTy,
        flattenHsForAllTyKeepAnns,
        hsExplicitTvs,
        hsTyVarName, mkHsWithBndrs, hsLKiTyVarNames,
        hsLTyVarName, hsLTyVarLocName, hsLTyVarLocNames,
        hsLTyVarBndrsToTypes,
        splitLHsInstDeclTy_maybe, splitLHsForAllTy,
        splitHsClassTy_maybe, splitLHsClassTy_maybe,
        splitHsFunType,
        splitHsAppTys, mkHsOpTy,
        ftvLHsType, ftvHsType,
        ignoreParens,

        -- Printing
        pprParendHsType, pprHsForAll, pprHsForAllExtra,
        pprHsContext, pprHsContextNoArrow, pprHsContextMaybe
    ) where

import {-# SOURCE #-} HsExpr ( HsSplice, pprSplice )

import PlaceHolder ( PostTc,PostRn,DataId,PlaceHolder(..) )

import Id ( Id )
import Name( Name, isTyVarName )
import Var ( varName )
import RdrName ( RdrName )
import DataCon( HsSrcBang(..), HsImplBang(..),
                SrcStrictness(..), SrcUnpackedness(..) )
import TysPrim( funTyConName )
import Type
import HsDoc
import BasicTypes
import SrcLoc
import StaticFlags
import Outputable
import FastString
import NameSet
import UniqFM ( mapUFM )
import Lexer ( AddAnn, mkParensApiAnn )
import Maybes( isJust )

import Data.Data hiding ( Fixity )
import Data.Maybe ( fromMaybe )
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid hiding ((<>))
#endif

{-
************************************************************************
*                                                                      *
\subsection{Bang annotations}
*                                                                      *
************************************************************************
-}

type LBangType name = Located (BangType name)
type BangType name  = HsType name       -- Bangs are in the HsType data type

getBangType :: LHsType a -> LHsType a
getBangType (L _ (HsBangTy _ ty)) = ty
getBangType ty                    = ty

getBangStrictness :: LHsType a -> HsSrcBang
getBangStrictness (L _ (HsBangTy s _)) = s
getBangStrictness _ = (HsSrcBang Nothing NoSrcUnpack NoSrcStrict)

{-
************************************************************************
*                                                                      *
\subsection{Data types}
*                                                                      *
************************************************************************

This is the syntax for types as seen in type signatures.

Note [HsBSig binder lists]
~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider a binder (or pattern) decoarated with a type or kind,
   \ (x :: a -> a). blah
   forall (a :: k -> *) (b :: k). blah
Then we use a LHsBndrSig on the binder, so that the
renamer can decorate it with the variables bound
by the pattern ('a' in the first example, 'k' in the second),
assuming that neither of them is in scope already
See also Note [Kind and type-variable binders] in RnTypes
-}

type LHsContext name = Located (HsContext name)
      -- ^ 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnUnit'

      -- For details on above see note [Api annotations] in ApiAnnotation

type HsContext name = [LHsType name]

type LHsType name = Located (HsType name)
      -- ^ May have 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnComma' when
      --   in a list

      -- For details on above see note [Api annotations] in ApiAnnotation
type HsKind name = HsType name
type LHsKind name = Located (HsKind name)
      -- ^ 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnDcolon'

      -- For details on above see note [Api annotations] in ApiAnnotation

--------------------------------------------------
--             LHsTyVarBndrs
--  The quantified binders in a HsForallTy

type LHsTyVarBndr name = Located (HsTyVarBndr name)

data LHsTyVarBndrs name
  = HsQTvs { hsq_implicit :: [name]               -- implicit (dependent) variables
           , hsq_explicit :: [LHsTyVarBndr name]  -- explicit variables
             -- See Note [HsForAllTy tyvar binders]
    }
  deriving( Typeable )
deriving instance (DataId name) => Data (LHsTyVarBndrs name)

mkHsQTvs :: [LHsTyVarBndr name] -> LHsTyVarBndrs name
-- Usually, this will be called at RdrName, but sometimes we
-- just need a LHsTyVarBndrs for impedance matching, and we don't
-- care about the implicit / explicit distinction. So, we allow
-- this to be called with any binder.
mkHsQTvs tvs = HsQTvs { hsq_implicit = [], hsq_explicit = tvs }

emptyHsQTvs :: LHsTyVarBndrs name   -- Use only when you know there are no implicit binders
emptyHsQTvs =  HsQTvs { hsq_implicit = [], hsq_explicit = [] }

hsQTvExplicit :: LHsTyVarBndrs name -> [LHsTyVarBndr name]
hsQTvExplicit = hsq_explicit

instance Monoid (LHsTyVarBndrs name) where
  mempty = emptyHsQTvs
  mappend (HsQTvs kvs1 tvs1) (HsQTvs kvs2 tvs2)
    = HsQTvs (kvs1 ++ kvs2) (tvs1 ++ tvs2)

------------------------------------------------
--            HsWithBndrs
-- Used to quantify the binders of a type in cases
-- when a HsForAll isn't appropriate:
--    * Patterns in a type/data family instance (HsTyPats)
--    * Type of a rule binder (RuleBndr)
--    * Pattern type signatures (SigPatIn)
-- In the last of these, wildcards can happen, so we must accommodate them

data HsWithBndrs name thing
  = HsWB { hswb_cts  :: thing                 -- Main payload (type or list of types)
         , hswb_vars :: PostRn name [Name]    -- Kind and type vars
         , hswb_wcs  :: PostRn name [Name]    -- Wild cards
    }
  deriving (Typeable)
deriving instance (DataId name, Data thing) => Data (HsWithBndrs name thing)

mkHsWithBndrs :: thing -> HsWithBndrs RdrName thing
mkHsWithBndrs x = HsWB { hswb_cts  = x
                       , hswb_vars = PlaceHolder
                       , hswb_wcs  = PlaceHolder }

--------------------------------------------------
-- | These names are used early on to store the names of implicit
-- parameters.  They completely disappear after type-checking.
newtype HsIPName = HsIPName FastString
  deriving( Eq, Data, Typeable )

hsIPNameFS :: HsIPName -> FastString
hsIPNameFS (HsIPName n) = n

instance Outputable HsIPName where
    ppr (HsIPName n) = char '?' <> ftext n -- Ordinary implicit parameters

instance OutputableBndr HsIPName where
    pprBndr _ n   = ppr n         -- Simple for now
    pprInfixOcc  n = ppr n
    pprPrefixOcc n = ppr n

--------------------------------------------------
data HsTyVarBndr name
  = UserTyVar        -- no explicit kinding
         name

  | KindedTyVar
         (Located name)
         (LHsKind name)  -- The user-supplied kind signature
        -- ^
        --  - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen',
        --          'ApiAnnotation.AnnDcolon', 'ApiAnnotation.AnnClose'

        -- For details on above see note [Api annotations] in ApiAnnotation
  deriving (Typeable)
deriving instance (DataId name) => Data (HsTyVarBndr name)

-- | Does this 'HsTyVarBndr' come with an explicit kind annotation?
isHsKindedTyVar :: HsTyVarBndr name -> Bool
isHsKindedTyVar (UserTyVar {})   = False
isHsKindedTyVar (KindedTyVar {}) = True

-- | Do all type variables in this 'LHsTyVarBndr' come with kind annotations?
hsTvbAllKinded :: LHsTyVarBndrs name -> Bool
hsTvbAllKinded = all (isHsKindedTyVar . unLoc) . hsQTvExplicit

data HsType name
  = HsForAllTy  HsExplicitFlag          -- Renamer leaves this flag unchanged, to record the way
                                        -- the user wrote it originally, so that the printer can
                                        -- print it as the user wrote it
                (Maybe SrcSpan)         -- Indicates whether extra constraints may be inferred.
                                        -- When Nothing, no, otherwise the location of the extra-
                                        -- constraints wildcard is stored. For instance, for the
                                        -- signature (Eq a, _) => a -> a -> Bool, this field would
                                        -- be something like (Just 1:8), with 1:8 being line 1,
                                        -- column 8.
                (LHsTyVarBndrs name)
                (LHsContext name)
                (LHsType name)
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnForall',
      --         'ApiAnnotation.AnnDot','ApiAnnotation.AnnDarrow'

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsTyVar             name            -- Type variable, type constructor, or data constructor
                                        -- see Note [Promotions (HsTyVar)]
      -- ^ - 'ApiAnnotation.AnnKeywordId' : None

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsAppsTy            [LHsAppType name]  -- Used only before renaming,
                                           -- Note [HsAppsTy]
      -- ^ - 'ApiAnnotation.AnnKeywordId' : None

  | HsAppTy             (LHsType name)
                        (LHsType name)
      -- ^ - 'ApiAnnotation.AnnKeywordId' : None

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsFunTy             (LHsType name)   -- function type
                        (LHsType name)
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnRarrow',

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsListTy            (LHsType name)  -- Element type
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @'['@,
      --         'ApiAnnotation.AnnClose' @']'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsPArrTy            (LHsType name)  -- Elem. type of parallel array: [:t:]
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @'[:'@,
      --         'ApiAnnotation.AnnClose' @':]'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsTupleTy           HsTupleSort
                        [LHsType name]  -- Element types (length gives arity)
    -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @'(' or '(#'@,
    --         'ApiAnnotation.AnnClose' @')' or '#)'@

    -- For details on above see note [Api annotations] in ApiAnnotation

  | HsOpTy              (LHsType name) (Located name) (LHsType name)
      -- ^ - 'ApiAnnotation.AnnKeywordId' : None

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsParTy             (LHsType name)   -- See Note [Parens in HsSyn] in HsExpr
        -- Parenthesis preserved for the precedence re-arrangement in RnTypes
        -- It's important that a * (b + c) doesn't get rearranged to (a*b) + c!
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @'('@,
      --         'ApiAnnotation.AnnClose' @')'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsIParamTy          HsIPName         -- (?x :: ty)
                        (LHsType name)   -- Implicit parameters as they occur in contexts
      -- ^
      -- > (?x :: ty)
      --
      -- - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnDcolon'

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsEqTy              (LHsType name)   -- ty1 ~ ty2
                        (LHsType name)   -- Always allowed even without TypeOperators, and has special kinding rule
      -- ^
      -- > ty1 ~ ty2
      --
      -- - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnTilde'

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsKindSig           (LHsType name)  -- (ty :: kind)
                        (LHsKind name)  -- A type with a kind signature
      -- ^
      -- > (ty :: kind)
      --
      -- - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @'('@,
      --         'ApiAnnotation.AnnDcolon','ApiAnnotation.AnnClose' @')'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsSpliceTy          (HsSplice name)   -- Includes quasi-quotes
                        (PostTc name Kind)
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @'$('@,
      --         'ApiAnnotation.AnnClose' @')'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsDocTy             (LHsType name) LHsDocString -- A documented type
      -- ^ - 'ApiAnnotation.AnnKeywordId' : None

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsBangTy    HsSrcBang (LHsType name)   -- Bang-style type annotations
      -- ^ - 'ApiAnnotation.AnnKeywordId' :
      --         'ApiAnnotation.AnnOpen' @'{-\# UNPACK' or '{-\# NOUNPACK'@,
      --         'ApiAnnotation.AnnClose' @'#-}'@
      --         'ApiAnnotation.AnnBang' @\'!\'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsRecTy     [LConDeclField name]    -- Only in data type declarations
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @'{'@,
      --         'ApiAnnotation.AnnClose' @'}'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsCoreTy Type       -- An escape hatch for tunnelling a *closed*
                        -- Core Type through HsSyn.
      -- ^ - 'ApiAnnotation.AnnKeywordId' : None

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsExplicitListTy       -- A promoted explicit list
        (PostTc name Kind) -- See Note [Promoted lists and tuples]
        [LHsType name]
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @"'["@,
      --         'ApiAnnotation.AnnClose' @']'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsExplicitTupleTy      -- A promoted explicit tuple
        [PostTc name Kind] -- See Note [Promoted lists and tuples]
        [LHsType name]
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnOpen' @"'("@,
      --         'ApiAnnotation.AnnClose' @')'@

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsTyLit HsTyLit      -- A promoted numeric literal.
      -- ^ - 'ApiAnnotation.AnnKeywordId' : None

      -- For details on above see note [Api annotations] in ApiAnnotation

  | HsWildCardTy (HsWildCardInfo name)  -- A type wildcard
      -- ^ - 'ApiAnnotation.AnnKeywordId' : None

      -- For details on above see note [Api annotations] in ApiAnnotation
  deriving (Typeable)
deriving instance (DataId name) => Data (HsType name)

-- Note [Literal source text] in BasicTypes for SourceText fields in
-- the following
data HsTyLit
  = HsNumTy SourceText Integer
  | HsStrTy SourceText FastString
    deriving (Data, Typeable)

mkHsOpTy :: LHsType name -> Located name -> LHsType name -> HsType name
mkHsOpTy ty1 op ty2 = HsOpTy ty1 op ty2

data HsWildCardInfo name
    = AnonWildCard (PostRn name Name)
      -- A anonymous wild card ('_'). A name is generated during renaming.
    | NamedWildCard name
      -- A named wild card ('_a').
    deriving (Typeable)
deriving instance (DataId name) => Data (HsWildCardInfo name)

type LHsAppType name = Located (HsAppType name)
data HsAppType name
  = HsAppInfix name                 -- either a symbol or an id in backticks
  | HsAppPrefix (HsType name)       -- anything else, including things like (+)
  deriving (Typeable)
deriving instance (DataId name) => Data (HsAppType name)

instance OutputableBndr name => Outputable (HsAppType name) where
  ppr (HsAppInfix n) = pprInfixOcc n

  ppr (HsAppPrefix (HsTyVar n)) = pprPrefixOcc n
  ppr (HsAppPrefix ty)          = ppr ty

{-
Note [HsForAllTy tyvar binders]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
After parsing:
  * Implicit => empty
    Explicit => the variables the user wrote

After renaming
  * Implicit => the *type* variables free in the type
    Explicit => the variables the user wrote (renamed)

Qualified currently behaves exactly as Implicit,
but it is deprecated to use it for implicit quantification.
In this case, GHC 7.10 gives a warning; see
Note [Context quantification] in RnTypes, and Trac #4426.
In GHC 7.12, Qualified will no longer bind variables
and this will become an error.

The kind variables bound in the hsq_implicit field come both
  a) from the kind signatures on the kind vars (eg k1)
  b) from the scope of the forall (eg k2)
Example:   f :: forall (a::k1) b. T a (b::k2)


Note [Unit tuples]
~~~~~~~~~~~~~~~~~~
Consider the type
    type instance F Int = ()
We want to parse that "()"
    as HsTupleTy HsBoxedOrConstraintTuple [],
NOT as HsTyVar unitTyCon

Why? Because F might have kind (* -> Constraint), so we when parsing we
don't know if that tuple is going to be a constraint tuple or an ordinary
unit tuple.  The HsTupleSort flag is specifically designed to deal with
that, but it has to work for unit tuples too.

Note [Promotions (HsTyVar)]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
HsTyVar: A name in a type or kind.
  Here are the allowed namespaces for the name.
    In a type:
      Var: not allowed
      Data: promoted data constructor
      Tv: type variable
      TcCls before renamer: type constructor, class constructor, or promoted data constructor
      TcCls after renamer: type constructor or class constructor
    In a kind:
      Var, Data: not allowed
      Tv: kind variable
      TcCls: kind constructor or promoted type constructor

Note [HsAppsTy]
~~~~~~~~~~~~~~~
How to parse

  Foo * Int

? Is it `(*) Foo Int` or `Foo GHC.Types.* Int`? There's no way to know until renaming.
So we just take type expressions like this and put each component in a list, so be
sorted out in the renamer. The sorting out is done by RnTypes.mkHsOpTyRn. This means
that the parser should never produce HsAppTy or HsOpTy.

Note [Promoted lists and tuples]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Notice the difference between
   HsListTy    HsExplicitListTy
   HsTupleTy   HsExplicitListTupleTy

E.g.    f :: [Int]                      HsListTy

        g3  :: T '[]                   All these use
        g2  :: T '[True]                  HsExplicitListTy
        g1  :: T '[True,False]
        g1a :: T [True,False]             (can omit ' where unambiguous)

  kind of T :: [Bool] -> *        This kind uses HsListTy!

E.g.    h :: (Int,Bool)                 HsTupleTy; f is a pair
        k :: S '(True,False)            HsExplicitTypleTy; S is indexed by
                                           a type-level pair of booleans
        kind of S :: (Bool,Bool) -> *   This kind uses HsExplicitTupleTy

Note [Distinguishing tuple kinds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Apart from promotion, tuples can have one of three different kinds:

        x :: (Int, Bool)                -- Regular boxed tuples
        f :: Int# -> (# Int#, Int# #)   -- Unboxed tuples
        g :: (Eq a, Ord a) => a         -- Constraint tuples

For convenience, internally we use a single constructor for all of these,
namely HsTupleTy, but keep track of the tuple kind (in the first argument to
HsTupleTy, a HsTupleSort). We can tell if a tuple is unboxed while parsing,
because of the #. However, with -XConstraintKinds we can only distinguish
between constraint and boxed tuples during type checking, in general. Hence the
four constructors of HsTupleSort:

        HsUnboxedTuple                  -> Produced by the parser
        HsBoxedTuple                    -> Certainly a boxed tuple
        HsConstraintTuple               -> Certainly a constraint tuple
        HsBoxedOrConstraintTuple        -> Could be a boxed or a constraint
                                        tuple. Produced by the parser only,
                                        disappears after type checking
-}

data HsTupleSort = HsUnboxedTuple
                 | HsBoxedTuple
                 | HsConstraintTuple
                 | HsBoxedOrConstraintTuple
                 deriving (Data, Typeable)

data HsExplicitFlag
  = Explicit     -- An explicit forall, eg  f :: forall a. a-> a
  | Implicit     -- No explicit forall, eg  f :: a -> a, or f :: Eq a => a -> a
  | Qualified    -- A *nested* occurrences of (ctxt => ty), with no explicit forall
                 -- e.g.  f :: (Eq a => a -> a) -> Int
 deriving (Data, Typeable)

type LConDeclField name = Located (ConDeclField name)
      -- ^ May have 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnComma' when
      --   in a list

      -- For details on above see note [Api annotations] in ApiAnnotation
data ConDeclField name  -- Record fields have Haddoc docs on them
  = ConDeclField { cd_fld_names :: [LFieldOcc name],
                                   -- ^ See Note [ConDeclField names]
                   cd_fld_type :: LBangType name,
                   cd_fld_doc  :: Maybe LHsDocString }
      -- ^ - 'ApiAnnotation.AnnKeywordId' : 'ApiAnnotation.AnnDcolon'

      -- For details on above see note [Api annotations] in ApiAnnotation
  deriving (Typeable)
deriving instance (DataId name) => Data (ConDeclField name)


type LFieldOcc name = Located (FieldOcc name)

-- | Represents an *occurrence* of an unambiguous field.  We store
-- both the 'RdrName' the user originally wrote, and after the
-- renamer, the selector function.
data FieldOcc name = FieldOcc { rdrNameFieldOcc  :: RdrName
                              , selectorFieldOcc :: PostRn name name
                              }
  deriving Typeable
deriving instance Eq (PostRn name name) => Eq (FieldOcc name)
deriving instance Ord (PostRn name name) => Ord (FieldOcc name)
deriving instance (Data name, Data (PostRn name name)) => Data (FieldOcc name)

instance Outputable (FieldOcc name) where
  ppr = ppr . rdrNameFieldOcc

mkFieldOcc :: RdrName -> FieldOcc RdrName
mkFieldOcc rdr = FieldOcc rdr PlaceHolder


-- | Represents an *occurrence* of a field that is potentially
-- ambiguous after the renamer, with the ambiguity resolved by the
-- typechecker.  We always store the 'RdrName' that the user
-- originally wrote, and store the selector function after the renamer
-- (for unambiguous occurrences) or the typechecker (for ambiguous
-- occurrences).
--
-- See Note [HsRecField and HsRecUpdField] in HsPat and
-- Note [Disambiguating record fields] in TcExpr.
data AmbiguousFieldOcc name
  = Unambiguous RdrName (PostRn name name)
  | Ambiguous   RdrName (PostTc name name)
  deriving (Typeable)
deriving instance ( Data name
                  , Data (PostRn name name)
                  , Data (PostTc name name))
                  => Data (AmbiguousFieldOcc name)

instance Outputable (AmbiguousFieldOcc name) where
  ppr = ppr . rdrNameAmbiguousFieldOcc

mkAmbiguousFieldOcc :: RdrName -> AmbiguousFieldOcc RdrName
mkAmbiguousFieldOcc rdr = Unambiguous rdr PlaceHolder

rdrNameAmbiguousFieldOcc :: AmbiguousFieldOcc name -> RdrName
rdrNameAmbiguousFieldOcc (Unambiguous rdr _) = rdr
rdrNameAmbiguousFieldOcc (Ambiguous   rdr _) = rdr

selectorAmbiguousFieldOcc :: AmbiguousFieldOcc Id -> Id
selectorAmbiguousFieldOcc (Unambiguous _ sel) = sel
selectorAmbiguousFieldOcc (Ambiguous   _ sel) = sel

unambiguousFieldOcc :: AmbiguousFieldOcc Id -> FieldOcc Id
unambiguousFieldOcc (Unambiguous rdr sel) = FieldOcc rdr sel
unambiguousFieldOcc (Ambiguous   rdr sel) = FieldOcc rdr sel

ambiguousFieldOcc :: FieldOcc name -> AmbiguousFieldOcc name
ambiguousFieldOcc (FieldOcc rdr sel) = Unambiguous rdr sel

{-
Note [ConDeclField names]
~~~~~~~~~~~~~~~~~~~~~~~~~

A ConDeclField contains a list of field occurrences: these always
include the field label as the user wrote it.  After the renamer, it
will additionally contain the identity of the selector function in the
second component.

Due to DuplicateRecordFields, the OccName of the selector function
may have been mangled, which is why we keep the original field label
separately.  For example, when DuplicateRecordFields is enabled

    data T = MkT { x :: Int }

gives

    ConDeclField { cd_fld_names = [L _ (FieldOcc "x" $sel:x:MkT)], ... }.
-}

-----------------------
-- A valid type must have a for-all at the top of the type, or of the fn arg
-- types

mkImplicitHsForAllTy  ::                                                 LHsType RdrName -> HsType RdrName
mkExplicitHsForAllTy  :: [LHsTyVarBndr RdrName] -> LHsContext RdrName -> LHsType RdrName -> HsType RdrName
mkQualifiedHsForAllTy ::                           LHsContext RdrName -> LHsType RdrName -> HsType RdrName

-- | mkImplicitHsForAllTy is called when we encounter
--    f :: type
-- Wrap around a HsForallTy if one is not there already.
mkImplicitHsForAllTy (L _ (HsForAllTy exp extra tvs cxt ty))
  = HsForAllTy exp' extra tvs cxt ty
  where
    exp' = case exp of
             Qualified -> Implicit
                          -- Qualified is used only for a nested forall,
                          -- this is now top level
             _         -> exp
mkImplicitHsForAllTy ty = mkHsForAllTy Implicit  [] (noLoc []) ty

mkExplicitHsForAllTy  tvs ctxt ty = mkHsForAllTy Explicit  tvs ctxt ty
mkQualifiedHsForAllTy     ctxt ty = mkHsForAllTy Qualified []  ctxt ty

-- |Smart constructor for HsForAllTy, which populates the extra-constraints
-- field if a wildcard is present in the context.
mkHsForAllTy :: HsExplicitFlag -> [LHsTyVarBndr RdrName] -> LHsContext RdrName -> LHsType RdrName -> HsType RdrName
mkHsForAllTy exp tvs ctxt ty
  = HsForAllTy exp Nothing (mkHsQTvs tvs) ctxt ty

-- |When a sigtype is parsed, the type found is wrapped in an Implicit
-- HsForAllTy via mkImplicitHsForAllTy, to ensure that a signature always has a
-- forall at the outer level. For Api Annotations this nested structure is
-- important to ensure that all `forall` and `.` locations are retained.  From
-- the renamer onwards this structure is flattened, to ease the renaming and
-- type checking process.
flattenTopLevelLHsForAllTy :: LHsType name -> LHsType name
flattenTopLevelLHsForAllTy (L l ty) = L l (flattenTopLevelHsForAllTy ty)

flattenTopLevelHsForAllTy :: HsType name -> HsType name
flattenTopLevelHsForAllTy (HsForAllTy exp extra tvs (L l []) ty)
  = snd $ mk_forall_ty [] l exp extra tvs ty
flattenTopLevelHsForAllTy ty = ty

flattenHsForAllTyKeepAnns :: HsType name -> ([AddAnn],HsType name)
flattenHsForAllTyKeepAnns (HsForAllTy exp extra tvs (L l []) ty)
  = mk_forall_ty [] l exp extra tvs ty
flattenHsForAllTyKeepAnns ty = ([],ty)

-- mk_forall_ty makes a pure for-all type (no context)
mk_forall_ty :: [AddAnn] -> SrcSpan -> HsExplicitFlag -> Maybe SrcSpan
             -> LHsTyVarBndrs name
             -> LHsType name -> ([AddAnn],HsType name)
mk_forall_ty ann _ exp1 extra1 tvs1 (L _ (HsForAllTy exp2 extra qtvs2 ctxt ty))
  = (ann,HsForAllTy (exp1 `plus` exp2) (mergeExtra extra1 extra)
                    (tvs1 `mappend` qtvs2) ctxt ty)
  where
        -- Bias the merging of extra's to the top level, so that a single
        -- wildcard context will prevail
        mergeExtra (Just s) _ = Just s
        mergeExtra _        e = e
mk_forall_ty ann l exp  extra tvs  (L lp (HsParTy ty))
  = mk_forall_ty (ann ++ mkParensApiAnn lp) l exp extra tvs ty
mk_forall_ty ann l exp extra tvs  ty
  = (ann,HsForAllTy exp extra tvs (L l []) ty)
        -- Even if tvs is empty, we still make a HsForAll!
        -- In the Implicit case, this signals the place to do implicit quantification
        -- In the Explicit case, it prevents implicit quantification
        --      (see the sigtype production in Parser.y)
        --      so that (forall. ty) isn't implicitly quantified

plus :: HsExplicitFlag -> HsExplicitFlag -> HsExplicitFlag
Qualified `plus` Qualified = Qualified
Explicit  `plus` _         = Explicit
_         `plus` Explicit  = Explicit
_         `plus` _         = Implicit
  -- NB: Implicit `plus` Qualified = Implicit
  --     so that  f :: Eq a => a -> a  ends up Implicit

---------------------
hsExplicitTvs :: LHsType Name -> [Name]
-- The explicitly-given forall'd type variables of a HsType
hsExplicitTvs (L _ (HsForAllTy Explicit _ tvs _ _)) = hsLKiTyVarNames tvs
hsExplicitTvs _                                     = []

---------------------
hsTyVarName :: HsTyVarBndr name -> name
hsTyVarName (UserTyVar n)           = n
hsTyVarName (KindedTyVar (L _ n) _) = n

hsLTyVarName :: LHsTyVarBndr name -> name
hsLTyVarName = hsTyVarName . unLoc

hsLKiTyVarNames :: LHsTyVarBndrs Name -> [Name]
-- Kind and type variables
hsLKiTyVarNames (HsQTvs { hsq_implicit = kvs, hsq_explicit = tvs })
  = kvs ++ map hsLTyVarName tvs

hsLTyVarLocName :: LHsTyVarBndr name -> Located name
hsLTyVarLocName = fmap hsTyVarName

hsLTyVarLocNames :: LHsTyVarBndrs name -> [Located name]
hsLTyVarLocNames qtvs = map hsLTyVarLocName (hsQTvExplicit qtvs)

-- | Convert a LHsTyVarBndr to an equivalent LHsType. Used in Template Haskell
-- quoting for type family equations.
hsLTyVarBndrToType :: LHsTyVarBndr name -> LHsType name
hsLTyVarBndrToType = fmap cvt
  where cvt (UserTyVar n)                     = HsTyVar n
        cvt (KindedTyVar (L name_loc n) kind) = HsKindSig (L name_loc (HsTyVar n))
                                                          kind

-- | Convert a LHsTyVarBndrs to a list of types. Used in Template Haskell
-- quoting for type family equations. Works on *type* variable only, no kind
-- vars.
hsLTyVarBndrsToTypes :: LHsTyVarBndrs name -> [LHsType name]
hsLTyVarBndrsToTypes (HsQTvs { hsq_explicit = tvbs }) = map hsLTyVarBndrToType tvbs

---------------------
mkAnonWildCardTy :: HsType RdrName
mkAnonWildCardTy = HsWildCardTy (AnonWildCard PlaceHolder)

mkNamedWildCardTy :: n -> HsType n
mkNamedWildCardTy = HsWildCardTy . NamedWildCard

isAnonWildCard :: HsWildCardInfo name -> Bool
isAnonWildCard (AnonWildCard _) = True
isAnonWildCard _                = False

isNamedWildCard :: HsWildCardInfo name -> Bool
isNamedWildCard = not . isAnonWildCard

wildCardName :: HsWildCardInfo Name -> Name
wildCardName (NamedWildCard n) = n
wildCardName (AnonWildCard  n) = n

-- Two wild cards are the same when: they're both named and have the same
-- name, or they're both anonymous and have the same location.
sameWildCard :: Eq name
             => Located (HsWildCardInfo name)
             -> Located (HsWildCardInfo name) -> Bool
sameWildCard (L l1 (AnonWildCard _))   (L l2 (AnonWildCard _))   = l1 == l2
sameWildCard (L _  (NamedWildCard n1)) (L _  (NamedWildCard n2)) = n1 == n2
sameWildCard _ _ = False

sameNamedWildCard :: Eq name
                  => Located (HsWildCardInfo name)
                  -> Located (HsWildCardInfo name) -> Bool
sameNamedWildCard (L _  (NamedWildCard n1)) (L _  (NamedWildCard n2)) = n1 == n2
sameNamedWildCard _ _ = False

splitHsAppTys :: LHsType Name -> [LHsType Name] -> (LHsType Name, [LHsType Name])
  -- no need to worry about HsAppsTy here
splitHsAppTys (L _ (HsAppTy f a)) as = splitHsAppTys f (a:as)
splitHsAppTys (L _ (HsParTy f))   as = splitHsAppTys f as
splitHsAppTys f                   as = (f,as)

splitLHsInstDeclTy_maybe
    :: LHsType Name
    -> Maybe (LHsTyVarBndrs Name, HsContext Name, Located Name, [LHsType Name])
        -- Split up an instance decl type, returning the pieces
splitLHsInstDeclTy_maybe inst_ty = do
    let (tvs, cxt, ty) = splitLHsForAllTy inst_ty
    (cls, tys) <- splitLHsClassTy_maybe ty
    return (tvs, cxt, cls, tys)

splitLHsForAllTy
    :: LHsType name
    -> (LHsTyVarBndrs name, HsContext name, LHsType name)
splitLHsForAllTy poly_ty
  = case unLoc poly_ty of
        HsParTy ty                -> splitLHsForAllTy ty
        HsForAllTy _ _ tvs cxt ty -> (tvs, unLoc cxt, ty)
        _                         -> (emptyHsQTvs, [], poly_ty)
        -- The type vars should have been computed by now, even if they were implicit

splitHsClassTy_maybe :: HsType Name -> Maybe (Name, [LHsType Name])
splitHsClassTy_maybe ty = fmap (\(L _ n, tys) -> (n, tys)) $ splitLHsClassTy_maybe (noLoc ty)

splitLHsClassTy_maybe :: LHsType Name -> Maybe (Located Name, [LHsType Name])
--- Watch out.. in ...deriving( Show )... we use this on
--- the list of partially applied predicates in the deriving,
--- so there can be zero args.

-- In TcDeriv we also use this to figure out what data type is being
-- mentioned in a deriving (Generic (Foo bar baz)) declaration (i.e. "Foo").
splitLHsClassTy_maybe ty
  = checkl ty []
  where
    checkl (L l ty) args = case ty of
        HsTyVar t          -> Just (L l t, args)
        HsAppTy l r        -> checkl l (r:args)
        HsOpTy l tc r      -> checkl (fmap HsTyVar tc) (l:r:args)
        HsParTy t          -> checkl t args
        HsKindSig ty _     -> checkl ty args
        _                  -> Nothing

-- splitHsFunType decomposes a type (t1 -> t2 ... -> tn)
-- Breaks up any parens in the result type:
--      splitHsFunType (a -> (b -> c)) = ([a,b], c)
-- Also deals with (->) t1 t2; that is why it only works on LHsType Name
--   (see Trac #9096)
splitHsFunType :: LHsType Name -> ([LHsType Name], LHsType Name)
splitHsFunType (L _ (HsParTy ty))
  = splitHsFunType ty

splitHsFunType (L _ (HsFunTy x y))
  | (args, res) <- splitHsFunType y
  = (x:args, res)

splitHsFunType orig_ty@(L _ (HsAppTy t1 t2))
  = go t1 [t2]
  where  -- Look for (->) t1 t2, possibly with parenthesisation
    go (L _ (HsTyVar fn))    tys | fn == funTyConName
                                 , [t1,t2] <- tys
                                 , (args, res) <- splitHsFunType t2
                                 = (t1:args, res)
    go (L _ (HsAppTy t1 t2)) tys = go t1 (t2:tys)
    go (L _ (HsParTy ty))    tys = go ty tys
    go _                     _   = ([], orig_ty)  -- Failure to match

splitHsFunType other = ([], other)

-- | Get the free Names of type variables in a renamed HsType
ftvLHsType :: LHsType Name -> NameSet
ftvLHsType (L _ ty) = ftvHsType ty

-- | Get the free Names of type variables in a renamed HsType
ftvHsType :: HsType Name -> NameSet
ftvHsType (HsForAllTy _ _ tvbs ctxt ty)
  = (ftvLHsContext ctxt `unionNameSet` ftvLHsType ty)
    `delListFromNameSet` hsLKiTyVarNames tvbs
ftvHsType (HsTyVar n)               = ftvName n
ftvHsType (HsAppsTy ts)             = unionNameSets $ map ftvLHsAppType ts
ftvHsType (HsAppTy t1 t2)           = ftvLHsType t1 `unionNameSet` ftvLHsType t2
ftvHsType (HsFunTy t1 t2)           = ftvLHsType t1 `unionNameSet` ftvLHsType t2
ftvHsType (HsListTy t)              = ftvLHsType t
ftvHsType (HsPArrTy t)              = ftvLHsType t
ftvHsType (HsTupleTy _ tys)         = unionNameSets $ map ftvLHsType tys
ftvHsType (HsOpTy t1 (L _ op) t2)
  = unionNameSets (ftvName op : map ftvLHsType [t1, t2])
ftvHsType (HsParTy t)               = ftvLHsType t
ftvHsType (HsIParamTy _ t)          = ftvLHsType t
ftvHsType (HsEqTy t1 t2)            = ftvLHsType t1 `unionNameSet` ftvLHsType t2
ftvHsType (HsKindSig t1 t2)         = ftvLHsType t1 `unionNameSet` ftvLHsType t2
ftvHsType (HsSpliceTy {})           = panic "ftvHsType HsSpliceTy"
ftvHsType (HsDocTy t _)             = ftvLHsType t
ftvHsType (HsBangTy _ t)            = ftvLHsType t
ftvHsType (HsRecTy {})              = panic "ftvHsType HsRecTy"
ftvHsType (HsCoreTy ty)             = mapUFM varName $ tyCoVarsOfType ty
ftvHsType (HsExplicitListTy _ tys)  = unionNameSets $ map ftvLHsType tys
ftvHsType (HsExplicitTupleTy _ tys) = unionNameSets $ map ftvLHsType tys
ftvHsType (HsTyLit {})              = emptyNameSet
ftvHsType (HsWildCardTy wc)         = ftvName (wildCardName wc)

ftvLHsAppType :: LHsAppType Name -> NameSet
ftvLHsAppType (L _ (HsAppInfix n))  = unitNameSet n
ftvLHsAppType (L _ (HsAppPrefix t)) = ftvHsType t

ftvLHsContext :: LHsContext Name -> NameSet
ftvLHsContext (L _ ctxt) = unionNameSets $ map ftvLHsType ctxt

ftvName :: Name -> NameSet
ftvName n
  | isTyVarName n = unitNameSet n
  | otherwise     = emptyNameSet

ignoreParens :: LHsType name -> LHsType name
ignoreParens (L _ (HsParTy ty)) = ignoreParens ty
ignoreParens ty                 = ty

{-
************************************************************************
*                                                                      *
\subsection{Pretty printing}
*                                                                      *
************************************************************************
-}

instance (OutputableBndr name) => Outputable (HsType name) where
    ppr ty = pprHsType ty

instance Outputable HsTyLit where
    ppr = ppr_tylit

instance (OutputableBndr name) => Outputable (LHsTyVarBndrs name) where
    ppr (HsQTvs { hsq_implicit = kvs, hsq_explicit = tvs })
      = ppr_kvs <+> interppSP tvs
      where
        ppr_kvs
          | [] <- kvs = empty
          | otherwise = braces (interppSP kvs)

instance (OutputableBndr name) => Outputable (HsTyVarBndr name) where
    ppr (UserTyVar n)     = ppr n
    ppr (KindedTyVar n k) = parens $ hsep [ppr n, dcolon, ppr k]

instance (Outputable thing) => Outputable (HsWithBndrs name thing) where
    ppr (HsWB { hswb_cts = ty }) = ppr ty

instance (Outputable name) => Outputable (HsWildCardInfo name) where
    ppr (AnonWildCard _)  = char '_'
    ppr (NamedWildCard n) = ppr n

pprHsForAll :: OutputableBndr name => HsExplicitFlag -> LHsTyVarBndrs name -> LHsContext name -> SDoc
pprHsForAll exp = pprHsForAllExtra exp Nothing

-- | Version of 'pprHsForAll' that can also print an extra-constraints
-- wildcard, e.g. @_ => a -> Bool@ or @(Show a, _) => a -> String@. This
-- underscore will be printed when the 'Maybe SrcSpan' argument is a 'Just'
-- containing the location of the extra-constraints wildcard. A special
-- function for this is needed, as the extra-constraints wildcard is removed
-- from the actual context and type, and stored in a separate field, thus just
-- printing the type will not print the extra-constraints wildcard.
pprHsForAllExtra :: OutputableBndr name => HsExplicitFlag -> Maybe SrcSpan -> LHsTyVarBndrs name -> LHsContext name -> SDoc
pprHsForAllExtra exp extra qtvs cxt
  | show_forall = forall_part <+> pprHsContextExtra show_extra (unLoc cxt)
  | otherwise   = pprHsContextExtra show_extra (unLoc cxt)
  where
    show_extra  = isJust extra
    show_forall =  opt_PprStyle_Debug
                || (not (null (hsQTvExplicit qtvs)) && is_explicit)
    is_explicit = case exp of {Explicit -> True; Implicit -> False; Qualified -> False}
    forall_part = forAllLit <+> ppr qtvs <> dot

pprHsContext :: (OutputableBndr name) => HsContext name -> SDoc
pprHsContext = maybe empty (<+> darrow) . pprHsContextMaybe

pprHsContextNoArrow :: (OutputableBndr name) => HsContext name -> SDoc
pprHsContextNoArrow = fromMaybe empty . pprHsContextMaybe

pprHsContextMaybe :: (OutputableBndr name) => HsContext name -> Maybe SDoc
pprHsContextMaybe []         = Nothing
pprHsContextMaybe [L _ pred] = Just $ ppr_mono_ty FunPrec pred
pprHsContextMaybe cxt        = Just $ parens (interpp'SP cxt)

-- True <=> print an extra-constraints wildcard, e.g. @(Show a, _) =>@
pprHsContextExtra :: (OutputableBndr name) => Bool -> HsContext name -> SDoc
pprHsContextExtra False = pprHsContext
pprHsContextExtra True
  = \ctxt -> case ctxt of
               [] -> char '_' <+> darrow
               _  -> parens (sep (punctuate comma ctxt')) <+> darrow
                 where ctxt' = map ppr ctxt ++ [char '_']

pprConDeclFields :: OutputableBndr name => [LConDeclField name] -> SDoc
pprConDeclFields fields = braces (sep (punctuate comma (map ppr_fld fields)))
  where
    ppr_fld (L _ (ConDeclField { cd_fld_names = ns, cd_fld_type = ty,
                                 cd_fld_doc = doc }))
        = ppr_names ns <+> dcolon <+> ppr ty <+> ppr_mbDoc doc
    ppr_names [n] = ppr n
    ppr_names ns = sep (punctuate comma (map ppr ns))

{-
Note [Printing KindedTyVars]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Trac #3830 reminded me that we should really only print the kind
signature on a KindedTyVar if the kind signature was put there by the
programmer.  During kind inference GHC now adds a PostTcKind to UserTyVars,
rather than converting to KindedTyVars as before.

(As it happens, the message in #3830 comes out a different way now,
and the problem doesn't show up; but having the flag on a KindedTyVar
seems like the Right Thing anyway.)
-}

-- Printing works more-or-less as for Types

pprHsType, pprParendHsType :: (OutputableBndr name) => HsType name -> SDoc

pprHsType ty       = getPprStyle $ \sty -> ppr_mono_ty TopPrec (prepare sty ty)
pprParendHsType ty = ppr_mono_ty TyConPrec ty

-- Before printing a type
-- (a) Remove outermost HsParTy parens
-- (b) Drop top-level for-all type variables in user style
--     since they are implicit in Haskell
prepare :: PprStyle -> HsType name -> HsType name
prepare sty (HsParTy ty)          = prepare sty (unLoc ty)
prepare _   ty                    = ty

ppr_mono_lty :: (OutputableBndr name) => TyPrec -> LHsType name -> SDoc
ppr_mono_lty ctxt_prec ty = ppr_mono_ty ctxt_prec (unLoc ty)

ppr_mono_ty :: (OutputableBndr name) => TyPrec -> HsType name -> SDoc
ppr_mono_ty ctxt_prec (HsForAllTy exp extra tvs ctxt ty)
  = maybeParen ctxt_prec FunPrec $
    sep [pprHsForAllExtra exp extra tvs ctxt, ppr_mono_lty TopPrec ty]

ppr_mono_ty _    (HsBangTy b ty)     = ppr b <> ppr_mono_lty TyConPrec ty
ppr_mono_ty _    (HsRecTy flds)      = pprConDeclFields flds
ppr_mono_ty _    (HsTyVar name)      = pprPrefixOcc name
ppr_mono_ty prec (HsFunTy ty1 ty2)   = ppr_fun_ty prec ty1 ty2
ppr_mono_ty _    (HsTupleTy con tys) = tupleParens std_con (pprWithCommas ppr tys)
  where std_con = case con of
                    HsUnboxedTuple -> UnboxedTuple
                    _              -> BoxedTuple
ppr_mono_ty _    (HsKindSig ty kind) = parens (ppr_mono_lty TopPrec ty <+> dcolon <+> ppr kind)
ppr_mono_ty _    (HsListTy ty)       = brackets (ppr_mono_lty TopPrec ty)
ppr_mono_ty _    (HsPArrTy ty)       = paBrackets (ppr_mono_lty TopPrec ty)
ppr_mono_ty prec (HsIParamTy n ty)   = maybeParen prec FunPrec (ppr n <+> dcolon <+> ppr_mono_lty TopPrec ty)
ppr_mono_ty _    (HsSpliceTy s _)    = pprSplice s
ppr_mono_ty _    (HsCoreTy ty)       = ppr ty
ppr_mono_ty _    (HsExplicitListTy _ tys) = quote $ brackets (interpp'SP tys)
ppr_mono_ty _    (HsExplicitTupleTy _ tys) = quote $ parens (interpp'SP tys)
ppr_mono_ty _    (HsTyLit t)         = ppr_tylit t
ppr_mono_ty _    (HsWildCardTy (AnonWildCard _))     = char '_'
ppr_mono_ty _    (HsWildCardTy (NamedWildCard name)) = ppr name

ppr_mono_ty ctxt_prec (HsEqTy ty1 ty2)
  = maybeParen ctxt_prec TyOpPrec $
    ppr_mono_lty TyOpPrec ty1 <+> char '~' <+> ppr_mono_lty TyOpPrec ty2

ppr_mono_ty ctxt_prec (HsAppsTy tys)
  = maybeParen ctxt_prec TyConPrec $
    hsep (map ppr tys)

ppr_mono_ty ctxt_prec (HsAppTy fun_ty arg_ty)
  = maybeParen ctxt_prec TyConPrec $
    hsep [ppr_mono_lty FunPrec fun_ty, ppr_mono_lty TyConPrec arg_ty]

ppr_mono_ty ctxt_prec (HsOpTy ty1 (L _ op) ty2)
  = maybeParen ctxt_prec TyOpPrec $
    sep [ ppr_mono_lty TyOpPrec ty1
        , sep [pprInfixOcc op, ppr_mono_lty TyOpPrec ty2 ] ]

ppr_mono_ty _         (HsParTy ty)
  = parens (ppr_mono_lty TopPrec ty)
  -- Put the parens in where the user did
  -- But we still use the precedence stuff to add parens because
  --    toHsType doesn't put in any HsParTys, so we may still need them

ppr_mono_ty ctxt_prec (HsDocTy ty doc)
  = maybeParen ctxt_prec TyOpPrec $
    ppr_mono_lty TyOpPrec ty <+> ppr (unLoc doc)
  -- we pretty print Haddock comments on types as if they were
  -- postfix operators

--------------------------
ppr_fun_ty :: (OutputableBndr name) => TyPrec -> LHsType name -> LHsType name -> SDoc
ppr_fun_ty ctxt_prec ty1 ty2
  = let p1 = ppr_mono_lty FunPrec ty1
        p2 = ppr_mono_lty TopPrec ty2
    in
    maybeParen ctxt_prec FunPrec $
    sep [p1, ptext (sLit "->") <+> p2]

--------------------------
ppr_tylit :: HsTyLit -> SDoc
ppr_tylit (HsNumTy _ i) = integer i
ppr_tylit (HsStrTy _ s) = text (show s)
