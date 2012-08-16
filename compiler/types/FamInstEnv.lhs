%
% (c) The University of Glasgow 2006
%

FamInstEnv: Type checked family instance declarations

\begin{code}
{-# OPTIONS -fno-warn-tabs #-}
-- The above warning supression flag is a temporary kludge.
-- While working on this module you are encouraged to remove it and
-- detab the module (please do the detabbing in a separate patch). See
--     http://hackage.haskell.org/trac/ghc/wiki/Commentary/CodingStyle#TabsvsSpaces
-- for details
{-# LANGUAGE ScopedTypeVariables #-}

module FamInstEnv (
	FamInstGroup(..), FamInst(..), FamFlavor(..), FamInstNewOrData(..),
        famInstAxiom, 
        famInstGroupInsts, famInstGroupTyCon, famInstGroupAxioms,
        famInstGroupIsData, famInstGroupName, famInstGroupFlavor,
        famInstGroupsRepTyCons, famInstRepTyCon_maybe,
        dataFamInstRepTyCon, dataFamInstGroupRepTyCon,
        famInstTys,
	pprFamInst, pprFamInsts, pprFamFlavor, pprFamInstGroups,
        pprFamInstGroupFlavor, pprFamInstGroup,
        mkSynFamInstGroup, mkDataFamInstGroup,
	mkSynFamInst, mkDataFamInst, mkImportedFamInst, mkImportedFamInstGroup,
        mkSingletonSynFamInstGroup, mkSingletonDataFamInstGroup,

	FamInstEnvs, FamInstEnv, emptyFamInstEnv, emptyFamInstEnvs, 
	extendFamInstEnv, deleteFromFamInstEnv, extendFamInstEnvList, 
	identicalFamInstGroup, identicalFamInst, famInstEnvElts, familyInstances,

        isDominatedBy,

        FamInstMatch(..),
        lookupFamInstEnv, lookupFamInstEnvConflicts, lookupFamInstEnvConflicts',
	
	-- Normalisation
	topNormaliseType, normaliseType, normaliseTcApp
    ) where

#include "HsVersions.h"

import InstEnv
import Unify
import Type
import TypeRep
import TyCon
import Coercion
import VarSet
import VarEnv
import Name
import UniqFM
import Outputable
import Maybes
import Util
import FastString
\end{code}


%************************************************************************
%*									*
\subsection{Type checked family instance heads}
%*									*
%************************************************************************

Note [FamInstGroups, FamInsts, and CoAxioms]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* CoAxioms and FamInsts are just like
  DFunIds  and ClsInsts

* A CoAxiom is a System-FC thing: it can relate any two types

* A FamInst is a Haskell source-language thing, corresponding
  to an individual type/data family instance declaration.  
    - The FamInst contains a CoAxiom, which is the evidence
      for the instance

    - The LHS of the CoAxiom is always of form F ty1 .. tyn
      where F is a type family

* A FamInstGroup is an ordered list of FamInsts. For example,

    type instance where
      Foo a a = Int
      Foo a b = Bool

  will be one FamInstGroup with two FamInsts.

Because there is no 'data instance where' construct, the list
of FamInsts will *always* contain exactly one FamInst when the
flavor is DataFamilyInst.

The list of FamInsts will *never* be empty.

\begin{code}
data FamInstGroup -- See Note [FamInstGroups, FamInsts, and CoAxioms]
  = FamInstGroup { fig_fis    :: [FamInst]
                 , fig_flavor :: FamFlavor

                  -- This field is the family tycon
                 , fig_fam_tc :: TyCon
                 , fig_fam    :: Name -- Family name
                  -- INVARIANT: fig_fam = name of fig_fam_tc
                 }

data FamInst  -- See Note [FamInstGroups, FamInsts, and CoAxioms]
  = FamInst { fi_axiom  :: CoAxiom      -- The new coercion axiom introduced
                                        -- by this family instance

            -- Everything below here is a redundant, 
            -- cached version of the field above
		-- Used for "rough matching"; same idea as for class instances
                -- See Note [Rough-match field] in InstEnv
	    , fi_tcs   :: [Maybe Name]	-- Top of type args
		-- INVARIANT: fi_tcs = roughMatchTcs fi_tys

		-- Used for "proper matching"; ditto
	    , fi_tvs    :: TyVarSet	-- Template tyvars for full match
	    , fi_tys    :: [Type]	-- arg types
		-- INVARIANT: fi_tvs = coAxiomTyVars fi_axiom
		--	      (_, fi_tys) = coAxiomSplitLHS fi_axiom

                -- The representation TyCon for a data instance
            , fi_rep_tc :: Maybe TyCon
                -- INVARIANT: if this represents a data instance,
                --            fi_rep_tc = Just rep_tc
                --            where (rep_tc, _) = splitTyConApp (co_ax_rhs fi_axiom)
            }

data FamFlavor 
  = SynFamilyInst                   -- A synonym family
  | DataFamilyInst FamInstNewOrData -- A data family

data FamInstNewOrData
  = FamInstNewType
  | FamInstDataType

\end{code}


\begin{code}
-- Obtain an ordered list of FamInsts from a FamInstGroup
famInstGroupInsts :: FamInstGroup -> [FamInst]
famInstGroupInsts = fig_fis

famInstGroupTyCon :: FamInstGroup -> TyCon
famInstGroupTyCon = fig_fam_tc

famInstGroupName :: FamInstGroup -> Name
famInstGroupName = fig_fam

famInstGroupFlavor :: FamInstGroup -> FamFlavor
famInstGroupFlavor = fig_flavor

famInstGroupIsData :: FamInstGroup -> Bool
famInstGroupIsData (FamInstGroup { fig_flavor = DataFamilyInst _ }) = True
famInstGroupIsData _                                                = False

famInstGroupAxioms :: FamInstGroup -> [CoAxiom]
famInstGroupAxioms = (map famInstAxiom) . famInstGroupInsts

-- Obtain the axiom of a family instance
famInstAxiom :: FamInst -> CoAxiom
famInstAxiom = fi_axiom

famInstTys :: FamInst -> [Type]
famInstTys = fi_tys

isDataFamInst :: FamInst -> Bool
isDataFamInst (FamInst { fi_rep_tc = Just _ }) = True
isDataFamInst _                                = False

-- Return the representation TyCons introduced by data family instances, if any
famInstGroupsRepTyCons :: [FamInstGroup] -> [TyCon]
famInstGroupsRepTyCons figs = [tc | FamInstGroup { fig_fis = fis } <- figs
                                  , FamInst { fi_rep_tc = Just tc } <- fis]

-- Extracts the TyCon for this *data* (or newtype) instance
famInstRepTyCon_maybe :: FamInst -> Maybe TyCon
famInstRepTyCon_maybe = fi_rep_tc

dataFamInstGroupRepTyCon :: FamInstGroup -> TyCon
dataFamInstGroupRepTyCon (FamInstGroup { fig_fis = [fam_inst] })
  = dataFamInstRepTyCon fam_inst
dataFamInstGroupRepTyCon fig = pprPanic "dataFamInstGroupRepTyCon" (ppr fig)

dataFamInstRepTyCon :: FamInst -> TyCon
dataFamInstRepTyCon fi 
  = case fi_rep_tc fi of
       Just tycon -> tycon
       Nothing    -> pprPanic "dataFamInstRepTyCon" (ppr fi)
\end{code}

\begin{code}
instance NamedThing FamInst where
  getName = coAxiomName . fi_axiom

-- We do NOT want an instance of NamedThing for FamInstGroup. Having one
-- would make it easy to apply getSrcSpan to a FamInstGroup. The only
-- reasonable behavior of getName would be to return the family name, which
-- has the SrcSpan of the family declaration, not the instance declaration.
-- If a chunk of code wants a SrcSpan from a FamInstGroup, it will have
-- to work for it or refactor some of the code in this file.

instance Outputable FamInst where
  ppr = pprFamInst

instance Outputable FamInstGroup where
  ppr = pprFamInstGroup

-- Prints the FamInst as a family instance declaration
pprFamInstGroup :: FamInstGroup -> SDoc
pprFamInstGroup (FamInstGroup { fig_fis = fis, fig_flavor = flav, fig_fam_tc = tc })
  | [fi] <- fis
  = let pp_instance
          | isTyConAssoc tc = empty
          | otherwise       = ptext (sLit "instance")
    in
    pprFamFlavor flav <+> pp_instance <+> pprFamInst fi

  | otherwise
  = ASSERT( case flav of { SynFamilyInst -> True ; DataFamilyInst _ -> False } )
    hang (ptext (sLit "type instance where"))
       2 (vcat (map pprFamInst fis))

pprFamInstGroups :: [FamInstGroup] -> SDoc
pprFamInstGroups = vcat . (map pprFamInstGroup)

pprFamInst :: FamInst -> SDoc
pprFamInst famInst
  = hang (pprFamInstHead famInst)
       2 (vcat [ ifPprDebug (ptext (sLit "Coercion axiom:") <+> ppr ax)
               , ifPprDebug (ptext (sLit "RHS:") <+> ppr (coAxiomRHS ax))
               , ptext (sLit "--") <+> pprDefinedAt (getName famInst)])
  where
    ax = fi_axiom famInst

pprFamInstHead :: FamInst -> SDoc
pprFamInstHead (FamInst {fi_axiom = axiom})
  = sep [ ifPprDebug (ptext (sLit "forall") <+> pprTvBndrs (coAxiomTyVars axiom))
        , pprTypeApp fam_tc tys ]    
  where
    (fam_tc, tys) = coAxiomSplitLHS axiom 
    
pprFamInsts :: [FamInst] -> SDoc
pprFamInsts finsts = vcat (map pprFamInst finsts)

-- uses natural English name; don't use where Haskell-like output is expected
pprFamInstGroupFlavor :: FamInstGroup -> SDoc
pprFamInstGroupFlavor (FamInstGroup { fig_fis = fis, fig_flavor = flav })
  | [_] <- fis
  = prefix
  | otherwise
  = prefix <+> ptext (sLit "group")
  where prefix = pprFamFlavor flav <+> ptext (sLit "instance")

pprFamFlavor :: FamFlavor -> SDoc
pprFamFlavor SynFamilyInst             = ptext (sLit "type")
pprFamFlavor (DataFamilyInst FamInstNewType)  = ptext (sLit "newtype")
pprFamFlavor (DataFamilyInst FamInstDataType) = ptext (sLit "data")

mkSynFamInstGroup :: TyCon        -- ^ Family tycon (@F@)
                  -> [FamInst]    -- ^ ordered list of family instances
                  -> FamInstGroup
mkSynFamInstGroup fam_tc fis
  = FamInstGroup { fig_fis    = fis
                 , fig_flavor = SynFamilyInst
                 , fig_fam_tc = fam_tc
                 , fig_fam    = tyConName fam_tc }

mkDataFamInstGroup :: TyCon     -- ^ Family tycon (@F@)
                   -> FamInst   -- ^ The one family instance in this group
                   -> FamInstGroup
mkDataFamInstGroup fam_tc fi@(FamInst { fi_rep_tc = Just rep_tc })
  = FamInstGroup { fig_fis    = [fi]
                 , fig_flavor = DataFamilyInst (mk_new_or_data rep_tc)
                 , fig_fam_tc = fam_tc
                 , fig_fam    = tyConName fam_tc }
mkDataFamInstGroup _ fi = pprPanic "mkDataFamInstGroup" (ppr fi)

-- | Create a coercion identifying a @type@ family instance.
-- It has the form @Co tvs :: F ts ~ R@, where @Co@ is 
-- the coercion constructor built here, @F@ the family tycon and @R@ the
-- right-hand side of the type family instance.
mkSynFamInst :: Name       -- ^ Unique name for the coercion tycon
             -> [TyVar]    -- ^ Type parameters of the coercion (@tvs@)
             -> TyCon      -- ^ Family tycon (@F@)
             -> [Type]     -- ^ Type instance (@ts@)
             -> Type       -- ^ Representation tycon (@R@)
             -> FamInst
mkSynFamInst name tvs fam_tc inst_tys rep_ty
  = FamInst { fi_tcs    = roughMatchTcs inst_tys
            , fi_tvs    = mkVarSet tvs
            , fi_tys    = inst_tys
            , fi_rep_tc = Nothing
            , fi_axiom  = axiom }
  where
    axiom = CoAxiom { co_ax_unique   = nameUnique name
                    , co_ax_name     = name
                    , co_ax_implicit = False
                    , co_ax_tvs      = tvs
                    , co_ax_lhs      = mkTyConApp fam_tc inst_tys 
                    , co_ax_rhs      = rep_ty }

-- | Create a coercion identifying a @data@ or @newtype@ representation type
-- and its family instance.  It has the form @Co tvs :: F ts ~ R tvs@,
-- where @Co@ is the coercion constructor built here, @F@ the family tycon
-- and @R@ the (derived) representation tycon.
mkDataFamInst :: Name       -- ^ Unique name for the coercion tycon
              -> [TyVar]    -- ^ Type parameters of the coercion (@tvs@)
              -> TyCon      -- ^ Family tycon (@F@)
              -> [Type]     -- ^ Type instance (@ts@)
              -> TyCon      -- ^ Representation tycon (@R@)
              -> FamInst
mkDataFamInst name tvs fam_tc inst_tys rep_tc
  = FamInst { fi_tcs    = roughMatchTcs inst_tys
            , fi_tvs    = mkVarSet tvs
            , fi_tys    = inst_tys
            , fi_rep_tc = Just rep_tc
            , fi_axiom  = axiom }
  where
    axiom = CoAxiom { co_ax_unique   = nameUnique name
                    , co_ax_name     = name
                    , co_ax_implicit = False
                    , co_ax_tvs      = tvs
                    , co_ax_lhs      = mkTyConApp fam_tc inst_tys 
                    , co_ax_rhs      = mkTyConApp rep_tc (mkTyVarTys tvs) }

mkSingletonSynFamInstGroup :: Name       -- ^ Unique name for the coercion tycon
                           -> [TyVar]    -- ^ Type parameters of the coercion (@tvs@)
                           -> TyCon      -- ^ Family tycon (@F@)
                           -> [Type]     -- ^ Type instance (@ts@)
                           -> Type       -- ^ Representation tycon (@R@)Name
                           -> FamInstGroup
mkSingletonSynFamInstGroup name tvs fam_tc inst_tys rep_ty
  = mkSynFamInstGroup fam_tc [mkSynFamInst name tvs fam_tc inst_tys rep_ty]

mkSingletonDataFamInstGroup :: Name       -- ^ Unique name for the coercion tycon
                            -> [TyVar]    -- ^ Type parameters of the coercion (@tvs@)
                            -> TyCon      -- ^ Family tycon (@F@)
                            -> [Type]     -- ^ Type instance (@ts@)
                            -> TyCon      -- ^ Representation tycon (@R@)
                            -> FamInstGroup
mkSingletonDataFamInstGroup name tvs fam_tc inst_tys rep_tc
  = mkDataFamInstGroup fam_tc (mkDataFamInst name tvs fam_tc inst_tys rep_tc)

-- Make a family instance representation from the information found in an
-- interface file.  In particular, we get the rough match info from the iface
-- (instead of computing it here).
mkImportedFamInstGroup :: Name          -- Name of the family
                       -> [FamInst]
                       -> FamInstGroup
mkImportedFamInstGroup fam fis
  = FamInstGroup { fig_fis    = fis
                 , fig_flavor = flavor
                 , fig_fam_tc = fam_tc 
                 , fig_fam    = fam }
  where
    head_fi = ASSERT( length fis > 0 )
              head fis
    axiom = famInstAxiom head_fi
    (fam_tc, _) = coAxiomSplitLHS axiom

    -- decide on the flavor based on whether or not there is a rep_tc 
    flavor = case fi_rep_tc head_fi of
               Just tc  -> DataFamilyInst (mk_new_or_data tc)
               Nothing -> SynFamilyInst

mk_new_or_data :: TyCon -> FamInstNewOrData
mk_new_or_data tc
  | isDataTyCon tc     = FamInstDataType
  | isNewTyCon tc      = FamInstNewType
  | isAbstractTyCon tc = FamInstDataType
  | otherwise          = pprPanic "mk_new_or_data" (ppr tc)

mkImportedFamInst :: [Maybe Name]       -- Rough match info
                  -> CoAxiom            -- Axiom introduced
                  -> FamInst            -- Resulting family instance
mkImportedFamInst mb_tcs axiom
  = FamInst {
      fi_tcs    = mb_tcs,
      fi_tvs    = mkVarSet . coAxiomTyVars $ axiom,
      fi_tys    = tys,
      fi_axiom  = axiom,
      fi_rep_tc = mrep_tc }

  where 
    (_, tys) = coAxiomSplitLHS axiom

         -- Derive the rep_tc for an imported FamInst rather disgustingly
         -- Maybe we should store it in the IfaceFamInst?
    mrep_tc  = case splitTyConApp_maybe (coAxiomRHS axiom) of
                 Just (tc, _)
                   | Just ax' <- tyConFamilyCoercion_maybe tc
                   , ax' == axiom
                   -> Just tc
                 _ -> Nothing

\end{code}



%************************************************************************
%*									*
		FamInstEnv
%*									*
%************************************************************************

Note [FamInstEnv]
~~~~~~~~~~~~~~~~~~~~~
A FamInstEnv maps a family name to the list of known instance groups for that
family.

The same FamInstEnv includes both 'data family' and 'type family' instances.
Type families are reduced during type inference, but not data families;
the user explains when to use a data family instance by using contructors
and pattern matching.

Neverthless it is still useful to have data families in the FamInstEnv:

 - For finding overlaps and conflicts

 - For finding the representation type...see FamInstEnv.topNormaliseType
   and its call site in Simplify

 - In standalone deriving instance Eq (T [Int]) we need to find the 
   representation type for T [Int]

\begin{code}
type FamInstEnv = UniqFM FamilyInstEnv	-- Maps a family to its instances
     -- See Note [FamInstEnv]

type FamInstEnvs = (FamInstEnv, FamInstEnv)
     -- External package inst-env, Home-package inst-env

data FamilyInstEnv
  = FamIE [FamInstGroup] -- The instance groups for a particular family,
                         -- in any order
  	  Bool 		 -- True <=> there is an instance of form T a b c
			 -- 	If *not* then the common case of looking up
			 --	(T a b c) can fail immediately

instance Outputable FamilyInstEnv where
  ppr (FamIE fs b) = ptext (sLit "FamIE") <+> ppr b <+> vcat (map ppr fs)

-- INVARIANTS:
--  * The fs_tvs are distinct in each FamInst
--	of a range value of the map (so we can safely unify them)

emptyFamInstEnvs :: (FamInstEnv, FamInstEnv)
emptyFamInstEnvs = (emptyFamInstEnv, emptyFamInstEnv)

emptyFamInstEnv :: FamInstEnv
emptyFamInstEnv = emptyUFM

famInstEnvElts :: FamInstEnv -> [FamInstGroup]
famInstEnvElts fi = [elt | FamIE elts _ <- eltsUFM fi, elt <- elts]

familyInstances :: (FamInstEnv, FamInstEnv) -> TyCon -> [FamInstGroup]
familyInstances (pkg_fie, home_fie) fam
  = get home_fie ++ get pkg_fie
  where
    get env = case lookupUFM env fam of
		Just (FamIE insts _) -> insts
		Nothing	             -> []

extendFamInstEnvList :: FamInstEnv -> [FamInstGroup] -> FamInstEnv
extendFamInstEnvList inst_env figs = foldl extendFamInstEnv inst_env figs

extendFamInstEnv :: FamInstEnv -> FamInstGroup -> FamInstEnv
extendFamInstEnv inst_env ins_item@(FamInstGroup {fig_fam = cls_nm, fig_fis = fis})
  = addToUFM_C add inst_env cls_nm (FamIE [ins_item] ins_tyvar)
  where
    add (FamIE items tyvar) _ = FamIE (ins_item:items)
				      (ins_tyvar || tyvar)
    ins_tyvar = or (map (not . any isJust . fi_tcs) fis)

deleteFromFamInstEnv :: FamInstEnv -> FamInstGroup -> FamInstEnv
deleteFromFamInstEnv inst_env fam_inst_grp@(FamInstGroup {fig_fam = fam_nm})
 = adjustUFM adjust inst_env fam_nm
 where
   adjust :: FamilyInstEnv -> FamilyInstEnv
   adjust (FamIE items tyvars)
     = FamIE (filterOut (identicalFamInstGroup fam_inst_grp) items) tyvars

identicalFamInstGroup :: FamInstGroup -> FamInstGroup -> Bool
identicalFamInstGroup (FamInstGroup { fig_fis = fis1 })
                      (FamInstGroup { fig_fis = fis2 })
  = and (zipWith identicalFamInst fis1 fis2)

identicalFamInst :: FamInst -> FamInst -> Bool
-- Same LHS, *and* the instance is defined in the same module
-- Used for overriding in GHCi
identicalFamInst (FamInst { fi_axiom = ax1 }) (FamInst { fi_axiom = ax2 })
  =  nameModule (coAxiomName ax1) == nameModule (coAxiomName ax2)
  && eqTypeX rn_env (coAxiomLHS ax1) (coAxiomLHS ax2)
  where
     tvs1 = coAxiomTyVars ax1
     tvs2 = coAxiomTyVars ax2
     rn_env = ASSERT( equalLength tvs1 tvs2 )
              rnBndrs2 (mkRnEnv2 emptyInScopeSet) tvs1 tvs2
                       
\end{code}

%************************************************************************
%*									*
		Looking up a family instance
%*									*
%************************************************************************

@lookupFamInstEnv@ looks up in a @FamInstEnv@, using a one-way match.
Multiple matches are only possible in case of type families (not data
families), and then, it doesn't matter which match we choose (as the
instances are guaranteed confluent).

We return the matching family instances and the type instance at which it
matches.  For example, if we lookup 'T [Int]' and have a family instance

  data instance T [a] = ..

desugared to

  data :R42T a = ..
  coe :Co:R42T a :: T [a] ~ :R42T a

we return the matching instance '(FamInst{.., fi_tycon = :R42T}, Int)'.

Note that the match process returns a FamInst, not a FamInstGroup. The
disambiguation among FamInsts within a group is done here.

Note [Instance checking within groups]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider the following:

type instance where
  F Int = Bool
  F a   = Int

g :: Show a => a -> F a
g x = length (show x)

Should that type-check? No. We need to allow for the possibility
that 'a' might be Int and therefore 'F a' should be Bool. We can
simplify 'F a' to Int only when we can be sure that 'a' is not Int.

To achieve this, after finding a possible match within an instance group, we
have to go back to all previous FamInsts and check that, under the
substitution induced by the match, other matches are not possible. This is
similar to what happens with class instance selection, when we need to
guarantee that there is only a match and no unifiers. The exact algorithm is
different here because the the potentially-overlapping group is closed.

ALTERNATE APPROACH: As we are processing the instance group, we could
check if an instance unifies but does not match. If this happens, there
is no possible match and we can fail right away. This might be more
efficient.

Note [Early failure optimisation for instance groups]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As we're searching through the instance groups for a match, it is
possible that we find an instance within a group that matches, but
a previous instance still unifies. In this case, we can abort the
search, because any other instance that matches will necessarily
overlap with the instance group we're currently searching. Because
overlap among instance groups is disallowed, we know that that
no such other instance exists.

Note [Confluence checking within groups]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider the following definition:

type family And (a :: Bool) (b :: Bool) :: Bool

type instance where
  And False a     = False
  And True  b     = b
  And c     False = False
  And d     True  = d

We wish to simplify (And e True). The search (using a one-way match
from type patterns to target) quickly eliminates the first three
possibilities. The fourth matches, with subst [d |-> e]. We then
go back and check the first three. We check each one to see if it
can possibly unify with the target (And e True). The first one does,
with subst [a |-> True, e |-> False]. To show that this is consistent
with the fourth equation, we must apply both substitutions to the
RHS of the fourth equation. Similarly, unifying with the second
equation gives us a subst [b |-> True, e |-> True], also requiring
the application of both substitutions to show consistency. The
third equation does not unify, so we're done and can simplify
(And e True) to e, as desired.

Why don't we just unify the two equations in the group? Because, in
general, we don't want to. Consider this:

type family F a b
type instance where
  F a a = Int
  F a b = b

We should be able to simplify (F x Int) but not (F y Bool). We need
the information from matching the target to differentiate these cases.

\begin{code}
data FamInstMatch 
  = FamInstMatch { fim_instance :: FamInst -- the matching FamInst
                 , fim_tys      :: [Type]  -- the substituted types
                                           -- See Note [Over-saturated matches]
                 , fim_group    :: FamInstGroup -- the group to which the match belongs
                   -- INVARIANT: fim_instance `elem` (famInstGroupInsts fim_group)
                 }

-- similarly used only in debugging
pprFamInstMatch :: FamInstMatch -> SDoc
pprFamInstMatch (FamInstMatch { fim_instance = inst
                              , fim_tys      = tys
                              , fim_group    = group })
  = hang (ptext (sLit "FamInstMatch {"))
       2 (vcat [ptext (sLit "fim_instance") <+> equals <+> ppr inst,
                ptext (sLit "fim_tys     ") <+> equals <+> ppr tys,
                ptext (sLit "fim_group   ") <+> equals <+> ppr group <+> ptext (sLit "}")])

instance Outputable FamInstMatch where
  ppr = pprFamInstMatch

lookupFamInstEnv
    :: FamInstEnvs
    -> TyCon -> [Type] -- What we are looking for
    -> [FamInstMatch]  -- Successful matches
-- Precondition: the tycon is saturated (or over-saturated)

lookupFamInstEnv
  = lookup_fam_inst_env match True
  where
    match group seen inst@(FamInst { fi_tvs = tpl_tvs,
                                     fi_tys = tpl_tys, fi_axiom = axiom })
          match_tys add_extra_tys
      = ASSERT( tyVarsOfTypes match_tys `disjointVarSet` tpl_tvs )
		-- Unification will break badly if the variables overlap
		-- They shouldn't because we allocate separate uniques for them
        case tcMatchTys tpl_tvs tpl_tys match_tys of
          -- success
          Just subst
            | checkUnify seen match_tys subst inst
            -> (Nothing, StopSearching) -- we found an incoherence, so stop searching
            -- see Note [Early failure optimisation for instance groups]

            | otherwise
            -> (Just $ FamInstMatch
                           { fim_instance = inst
                           , fim_tys      = add_extra_tys $
                                            substTyVars subst (coAxiomTyVars axiom)
                           , fim_group    = group }, KeepSearching)

          -- failure; instance not relevant
          Nothing -> (Nothing, KeepSearching) 
    
    -- see Note [Instance checking within groups]
    checkUnify :: [FamInst] -- the previous FamInsts in the group that matched
               -> [Type]    -- the types in the tyfam application we are matching
               -> TvSubst   -- the subst that witnesses the match between those types and...
               -> FamInst   -- ...this FamInst
               -> Bool      -- is there a conflicting unification?
    checkUnify [] _ _ _ = False
    checkUnify ((FamInst { fi_tys = tpl_tys
                         , fi_axiom = inner_axiom }) : rest)
               match_tys outer_subst
               outer_fi@(FamInst { fi_axiom = outer_axiom })
      | Just inner_subst <- tcUnifyTys instanceBindFun tpl_tys match_tys
      -- see Note [Confluence checking within groups]
      = let outer_tvs = coAxiomTyVars outer_axiom
            inner_tvs = coAxiomTyVars inner_axiom
            outer_rhs = mkAxInstRHS outer_axiom (substTys inner_subst $
                                                 substTyVars outer_subst outer_tvs)
            inner_rhs = mkAxInstRHS inner_axiom (substTyVars inner_subst inner_tvs)
        in not (outer_rhs `eqType` inner_rhs)
      | otherwise
      = checkUnify rest match_tys outer_subst outer_fi


lookupFamInstEnvConflicts
    :: FamInstEnvs
    -> TyCon            -- family tycon
    -> [FamInst]        -- the instances that came before the current one
                        -- in the group
    -> FamInst		-- Putative new instance
    -> [TyVar]		-- Unique tyvars, matching arity of FamInst
    -> [FamInst] 	-- Conflicting FamInsts
-- E.g. when we are about to add
--    f : type instance F [a] = a->a
-- we do (lookupFamInstConflicts f [b])
-- to find conflicting matches
-- The skolem tyvars are needed because we don't have a 
-- unique supply to hand
--
-- Precondition: the tycon is saturated (or over-saturated)

lookupFamInstEnvConflicts envs fam prev_insts fam_inst skol_tvs
  = lookup_fam_inst_env my_unify False envs fam tys1
  where
    inst_axiom = famInstAxiom fam_inst
    tys        = famInstTys fam_inst
    skol_tys   = mkTyVarTys skol_tvs
    tys1       = substTys (zipTopTvSubst (coAxiomTyVars inst_axiom) skol_tys) tys
        -- In example above,   fam tys' = F [b]   

    -- my_unify returns Maybe (Maybe FamInst)
    -- Nothing --> keep searching within group
    -- Just Nothing --> stop searching within group; no conflict
    -- Just (Just inst) --> found a conflict with inst
    my_unify _ seen old_fam_inst@(FamInst { fi_tvs = tpl_tvs, fi_tys = tpl_tys })
             match_tys _
       -- (Case 2) in [Family instance overlap conflicts]
       | tpl_tys `isDominatedBy` prev_insts
       = (Nothing, KeepSearching)
       | otherwise
       = ASSERT2( tyVarsOfTypes tys1 `disjointVarSet` tpl_tvs,
		  (ppr fam_inst <+> ppr tys1) $$
		  (ppr tpl_tvs <+> ppr tpl_tys) )
		-- Unification will break badly if the variables overlap
		-- They shouldn't because we allocate separate uniques for them
         case tcUnifyTys instanceBindFun tpl_tys match_tys of
	      Just subst
                | rhs_conflict old_fam_inst skol_tvs inst_axiom subst
                -> (Just old_fam_inst, KeepSearching)
                -- (Case 1) in [Family instance overlap conflicts]
                | match_tys `isDominatedBy` (old_fam_inst : seen)
                -> (Nothing, StopSearchingThisGroup)
                | otherwise -- confluent overlap
                -> (Nothing, KeepSearching)
	      -- irrelevant instance
              Nothing -> (Nothing, KeepSearching)

-- checks whether two RHSs are distinct, under a unifying substitution
-- Note [Family instance overlap conflicts]
rhs_conflict :: FamInst -> [TyVar] -> CoAxiom -> TvSubst -> Bool
rhs_conflict fi1@(FamInst { fi_axiom = axiom1 })
             tvs2 axiom2 subst 
  | isDataFamInst fi1
  = True
  | otherwise
  = not (rhs1 `eqType` rhs2)
    where
      tvs1 = coAxiomTyVars axiom1
      rhs1 = mkAxInstRHS axiom1 (substTyVars subst tvs1)
      rhs2 = mkAxInstRHS axiom2 (substTyVars subst tvs2)

-- This variant is called when we want to check if the conflict is only in the
-- home environment (see FamInst.addLocalFamInst)
lookupFamInstEnvConflicts' :: FamInstEnv -> TyCon
                           -> [FamInst] -> FamInst -> [TyVar] -> [FamInst]
lookupFamInstEnvConflicts' env
  = lookupFamInstEnvConflicts (emptyFamInstEnv, env)
\end{code}

Note [lookup_fam_inst_env' implementation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To reduce code duplication, both lookups during simplification and conflict
checking are routed through lookup_fam_inst_env', which looks for a
matching/unifying instance compared to some target. In the simplification
case, the search is for a match for a target application; in the conflict-
checking case, the search is for a unifier for a putative new family instance.

The two uses are differentiated by different MatchFuns, which look at a
given instance to see if it is relevant and whether the search should continue.
The the instance is relevant (i.e. matches, or unifies in a conflicting manner),
Just <something> is returned; if the instance is not relevant, Nothing is returned.
The MatchFun also indicates what the search algorithm should do next: it could
KeepSearching, StopSearching altogether, or just StopSearchingThisGroup but
continue to search others.

When to StopSearching? See Note [Early failure optimisation for instance groups]
When to StopSearchingThisGroup? See Note [Family instance overlap conflicts] (case 1)

For class instances, these two variants of lookup are combined into one
function (cf, @InstEnv@).  We don't do that for family instances as the
results of matching and unification are used in two different contexts.
Moreover, matching is the wildly more frequently used operation in the case of
indexed synonyms and we don't want to slow that down by needless unification.

Note [Family instance overlap conflicts]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
- In the case of data family instances, any overlap is fundamentally a
  conflict (as these instances imply injective type mappings).

- In the case of type family instances, overlap is admitted as long as
  the right-hand sides of the overlapping rules coincide under the
  overlap substitution.  eg
       type instance F a Int = a
       type instance F Int b = b
  These two overlap on (F Int Int) but then both RHSs are Int, 
  so all is well. We require that they are syntactically equal;
  anything else would be difficult to test for at this stage.

How is this implemented? Consider this:

type family F a b
type instance where
  F a a = Char
  F a b = Double
type instance F Int Int = Char

This code contains no conflicts. But, a naive implementation would eventually
try to unify (F a b) and (F Int Int), succeed, and discover that the RHSs do
not coincide. We wish to avoid this problem. There are two cases to consider:

(Case 1): The instances are checked in the order written above.
We are trying to see if the (F Int Int) instance has any conflicts. So, we
search through all pre-existing instance groups to see if there are unifiers.
As we search through the one group written above, we want to stop after
checking the first equation. Why? Because any application of F that matches
(F Int Int) also necessarily matches (F a a). Thus, any later equations in
the group are irrelevant for checking the consistency of (F Int Int). In
general, as the search proceeds through a group, it collects a list of
equations that have already been checked. When this list dominates the
instance we are checking for consistency, we can StopSearchingThisGroup.
The equation that, when added to the list, causes the list to dominate
the new instance must also unify, so we check for this condition in the
context of a successful unification.

(Case 2): The instances are checked in the reverse order as written above.
Here, the interesting case is when we are checking (F a b) for consistency.
We need to avoid checking against the (F Int Int) case. The condition is,
in effect, the same as in (Case 1). We avoid checking (F Int Int) when
all the instances previous to (F a b) in (F a b)'s group dominate (F Int Int).
The check is coded rather differently because the context is different, but
the net effect is the same. Note that we don't wish to StopSearchingThisGroup,
because perhaps the analogue of (F Int Int) is in an instance group such that
a later equation is relevant. We simply wish to say that there is no conflict
on this equation.

\begin{code}
------------------------------------------------------------
data ContSearch = KeepSearching
                | StopSearching
                | StopSearchingThisGroup -- (but keep searching others)

-- Might be a one-way match or a unifier
type MatchFun a =  FamInstGroup        -- the group in which we are checking
                -> [FamInst]           -- the previous FamInsts in the group
                -> FamInst             -- the individual FamInst to check
                -> [Type]              -- the types to match against
                -> ([Type] -> [Type])  -- see add_extra_tys, below
                -> (Maybe a, ContSearch)

-- informs why we are doing a lookup. See Note [Family instance overlap conflicts]
type OneSidedMatch = Bool -- whether or not we can optimise for matching

lookup_fam_inst_env' 	      -- The worker, local to this module
    :: forall a. MatchFun a
    -> OneSidedMatch
    -> FamInstEnv
    -> TyCon -> [Type]		-- What we are looking for
    -> [a] 
lookup_fam_inst_env' match_fun one_sided ie fam tys
  | not (isFamilyTyCon fam) 
  = []
  | otherwise
  = ASSERT2( n_tys >= arity, ppr fam <+> ppr tys )	-- Family type applications must be saturated
    lookup ie
  where
    -- See Note [Over-saturated matches]
    arity = tyConArity fam
    n_tys = length tys
    extra_tys = drop arity tys
    (match_tys, add_extra_tys) 
       | arity < n_tys = (take arity tys, \res_tys -> res_tys ++ extra_tys)
       | otherwise     = (tys,            \res_tys -> res_tys)
       	 -- The second case is the common one, hence functional representation

    --------------
    rough_tcs = roughMatchTcs match_tys
    all_tvs   = all isNothing rough_tcs && one_sided

    --------------
    lookup env = case lookupUFM env fam of
		   Nothing -> []	-- No instances for this family
		   Just (FamIE groups has_tv_insts)
		       -- Short cut for common case:
		       --   The thing we are looking up is of form (C a
		       --   b c), and the FamIE has no instances of
		       --   that form, so don't bother to search 
		     | all_tvs && not has_tv_insts -> []
		     | otherwise                   -> findGroup groups

    --------------
    findGroup :: [FamInstGroup] -> [a]
    findGroup [] = []
    findGroup (group@(FamInstGroup { fig_fis = fam_insts }) : rest)
      = case findInst group [] fam_insts of
          (Just match, False) -> [match]
          (Just match, True)  -> match : findGroup rest
          (Nothing,    False) -> []
          (Nothing,    True)  -> findGroup rest

    findInst :: FamInstGroup -- the group in which we are checking
             -> [FamInst]    -- the FamInsts that have already been checked
             -> [FamInst]    -- still looking through these
             -> (Maybe a, Bool) -- Bool indicates whether to continue
    findInst _ _ [] = (Nothing, True)
    findInst group seen (head_inst@(FamInst { fi_tcs = mb_tcs }) : rest)
      | instanceCantMatch rough_tcs mb_tcs
      = findInst group seen rest -- head_inst looks fundamentally different; ignore
      | otherwise
      = case match_fun group seen head_inst match_tys add_extra_tys of
          (Just result, StopSearching)      -> (Just result, False)
          (Just result, _)                  -> (Just result, True)
          (Nothing, StopSearchingThisGroup) -> (Nothing, True)
          (Nothing, StopSearching)          -> (Nothing, False)
          (Nothing, KeepSearching)          -> findInst group (head_inst : seen) rest

-- checks if one LHS is dominated by a list of other LHSs
-- in other words, if an application would match the first LHS, it is guaranteed
-- to match at least one of the others. The RHSs are ignored.
-- TODO: Write a complete algorithm
isDominatedBy :: [Type] -> [FamInst] -> Bool
isDominatedBy tys1 fi2s
  = -- The current algorithm has false negatives but no false positives
    -- That state of affairs makes the checking algorithm sound though incomplete
    or $ map match fi2s
    where
      match (FamInst { fi_tvs = tvs2, fi_tys = tys2 })
        = isJust $ tcMatchTys tvs2 tys2 tys1

-- Precondition: the tycon is saturated (or over-saturated)

lookup_fam_inst_env 	      -- The worker, local to this module
    :: MatchFun a
    -> OneSidedMatch
    -> FamInstEnvs
    -> TyCon -> [Type]        -- What we are looking for
    -> [a]                    -- Successful matches

-- Precondition: the tycon is saturated (or over-saturated)
lookup_fam_inst_env match_fun one_sided (pkg_ie, home_ie) fam tys = 
    lookup_fam_inst_env' match_fun one_sided home_ie fam tys ++
    lookup_fam_inst_env' match_fun one_sided pkg_ie  fam tys

\end{code}

Note [Over-saturated matches]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It's ok to look up an over-saturated type constructor.  E.g.
     type family F a :: * -> *
     type instance F (a,b) = Either (a->b)

The type instance gives rise to a newtype TyCon (at a higher kind
which you can't do in Haskell!):
     newtype FPair a b = FP (Either (a->b))

Then looking up (F (Int,Bool) Char) will return a FamInstMatch 
     (FPair, [Int,Bool,Char])

The "extra" type argument [Char] just stays on the end.


%************************************************************************
%*									*
		Looking up a family instance
%*									*
%************************************************************************

\begin{code}
topNormaliseType :: FamInstEnvs
		 -> Type
	   	 -> Maybe (Coercion, Type)

-- Get rid of *outermost* (or toplevel) 
--	* type functions 
--	* newtypes
-- using appropriate coercions.
-- By "outer" we mean that toplevelNormaliseType guarantees to return
-- a type that does not have a reducible redex (F ty1 .. tyn) as its
-- outermost form.  It *can* return something like (Maybe (F ty)), where
-- (F ty) is a redex.

-- Its a bit like Type.repType, but handles type families too

topNormaliseType env ty
  = go [] ty
  where
    go :: [TyCon] -> Type -> Maybe (Coercion, Type)
    go rec_nts ty | Just ty' <- coreView ty 	-- Expand synonyms
	= go rec_nts ty'	

    go rec_nts (TyConApp tc tys)
        | isNewTyCon tc		-- Expand newtypes
	= if tc `elem` rec_nts 	-- See Note [Expanding newtypes] in Type.lhs
	  then Nothing
          else let nt_co = mkAxInstCo (newTyConCo tc) tys
               in add_co nt_co rec_nts' nt_rhs

	| isFamilyTyCon tc		-- Expand open tycons
	, (co, ty) <- normaliseTcApp env tc tys
		-- Note that normaliseType fully normalises 'tys', 
		-- It has do to so to be sure that nested calls like
		--    F (G Int)
		-- are correctly top-normalised
        , not (isReflCo co)
        = add_co co rec_nts ty
        where
          nt_rhs = newTyConInstRhs tc tys
          rec_nts' | isRecursiveTyCon tc = tc:rec_nts
                   | otherwise           = rec_nts

    go _ _ = Nothing

    add_co co rec_nts ty 
	= case go rec_nts ty of
		Nothing 	-> Just (co, ty)
		Just (co', ty') -> Just (mkTransCo co co', ty')
	 

---------------
normaliseTcApp :: FamInstEnvs -> TyCon -> [Type] -> (Coercion, Type)
normaliseTcApp env tc tys
  | isFamilyTyCon tc
  , tyConArity tc <= length tys	   -- Unsaturated data families are possible
  , [FamInstMatch { fim_instance = fam_inst
                  , fim_tys      = inst_tys }] <- lookupFamInstEnv env tc ntys 
  = let    -- A matching family instance exists
        ax              = famInstAxiom fam_inst
        co              = mkAxInstCo  ax inst_tys
        rhs             = mkAxInstRHS ax inst_tys
	first_coi       = mkTransCo tycon_coi co
	(rest_coi,nty)  = normaliseType env rhs
	fix_coi         = mkTransCo first_coi rest_coi
    in 
    (fix_coi, nty)

  | otherwise   -- No unique matching family instance exists;
		-- we do not do anything
  = (tycon_coi, TyConApp tc ntys)

  where
	-- Normalise the arg types so that they'll match 
	-- when we lookup in in the instance envt
    (cois, ntys) = mapAndUnzip (normaliseType env) tys
    tycon_coi    = mkTyConAppCo tc cois

---------------
normaliseType :: FamInstEnvs 		-- environment with family instances
	      -> Type  			-- old type
	      -> (Coercion, Type)	-- (coercion,new type), where
					-- co :: old-type ~ new_type
-- Normalise the input type, by eliminating *all* type-function redexes
-- Returns with Refl if nothing happens

normaliseType env ty 
  | Just ty' <- coreView ty = normaliseType env ty' 
normaliseType env (TyConApp tc tys)
  = normaliseTcApp env tc tys
normaliseType _env ty@(LitTy {}) = (Refl ty, ty)
normaliseType env (AppTy ty1 ty2)
  = let (coi1,nty1) = normaliseType env ty1
        (coi2,nty2) = normaliseType env ty2
    in  (mkAppCo coi1 coi2, mkAppTy nty1 nty2)
normaliseType env (FunTy ty1 ty2)
  = let (coi1,nty1) = normaliseType env ty1
        (coi2,nty2) = normaliseType env ty2
    in  (mkFunCo coi1 coi2, mkFunTy nty1 nty2)
normaliseType env (ForAllTy tyvar ty1)
  = let (coi,nty1) = normaliseType env ty1
    in  (mkForAllCo tyvar coi, ForAllTy tyvar nty1)
normaliseType _   ty@(TyVarTy _)
  = (Refl ty,ty)
\end{code}
