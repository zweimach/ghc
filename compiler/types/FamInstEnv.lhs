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

module FamInstEnv (
	FamInst(..), FamFlavor(..), FamInstBranch(..),
        famInstAxiom, famInstBranchRoughMatch,
        famInstsRepTyCons, famInstNthBranch, famInstSingleBranch,
        famInstBranchLHS,
        famInstTyCon, famInstRepTyCon_maybe, dataFamInstRepTyCon, 
	pprFamInst, pprFamInsts, pprFamInstBranch, pprFamInstBranches,
        pprFamFlavor,
	mkSynFamInst, mkSynFamInstBranch, mkSingleSynFamInst,
        mkDataFamInst, mkImportedFamInst,

	FamInstEnvs, FamInstEnv, emptyFamInstEnv, emptyFamInstEnvs, 
	extendFamInstEnv, deleteFromFamInstEnv, extendFamInstEnvList, 
	identicalFamInst, famInstEnvElts, familyInstances,

        FamInstMatch(..),
	lookupFamInstEnv, lookupFamInstEnvConflicts, lookupFamInstEnvConflicts',
	
        isDominatedBy,

	-- Normalisation
	topNormaliseType, normaliseType, normaliseTcApp
    ) where

#include "HsVersions.h"

import InstEnv
import Unify
import Type
import Coercion hiding ( substTy )
import TypeRep
import TyCon
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

Note [FamInsts and CoAxioms]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* CoAxioms and FamInsts are just like
  DFunIds  and ClsInsts

* A CoAxiom is a System-FC thing: it can relate any two types

* A FamInst is a Haskell source-language thing, corresponding
  to a type/data family instance declaration.  
    - The FamInst contains a CoAxiom, which is the evidence
      for the instance

    - The LHSs of the CoAxiom branches are always of form
      F ty1 .. tyn where F is a type family

* A FamInstBranch corresponds to a CoAxBranch -- it represents
  one alternative in a family instance group. It is needed solely
  to keep Haskell-like things separate from FC-like things.

Note [Single FamInsts]
~~~~~~~~~~~~~~~~~~~~~~
Although FamInsts support multiple branches, there are many places
throughout GHC where we know that a FamInst (or its CoAxiom) really
should have only one branch. For examples: associated type/data families,
any data families, instances created by derivation/vectorisation.
So, there are a number of functions that operate with the assumption
that there is only one branch. All of these functions have "Single"
in their name. If you are increasing the set of things that might
have multiple branches, you should search for "Single" throughout
GHC and make sure you're not violating any assumptions made elsewhere.

This is a little ugly. However, the two alternatives are uglier: either
have a separate type for singleton FamInsts/CoAxioms and repeat a whole
lot of code, or track a branch choice in a whole lot of places where it
is unnecessary. Perhaps a third alternative is to use a phantom Boolean
type index on FamInst indicating its singlehood. That may be an idea
for the future.

\begin{code}
data FamInst  -- See Note [FamInsts and CoAxioms]
  = FamInst { fi_axiom    :: CoAxiom         -- The new coercion axiom introduced
                                             -- by this family instance
            , fi_flavor   :: FamFlavor
            , fi_group    :: Bool            -- True <=> declared with "type instance where"
                -- INVARIANT: not fi_group implies co_ax_arity (fi_axiom) == 1.

            -- Everything below here is a redundant, 
            -- cached version of the two things above
            , fi_branches :: [FamInstBranch] -- Haskell-source-language view of 
                                             -- a CoAxBranch
            , fi_fam      :: Name	     -- Family name
		-- INVARIANT: fi_fam = name of fi_axiom.co_ax_tc
            }

data FamInstBranch
  = FamInstBranch
    { fib_fam_tc :: TyCon        -- family tycon (same for all branches,
                                 -- but in different locations)
    , fib_tvs    :: TyVarSet     -- bound type variables
    , fib_lhs    :: [Type]       -- type patterns
    , fib_rhs    :: Type         -- RHS of family instance
    , fib_tcs    :: [Maybe Name] -- used for "rough matching" during typechecking
                                 -- see Note [Rough-match field] in InstEnv
    }

data FamFlavor 
  = SynFamilyInst         -- A synonym family
  | DataFamilyInst TyCon  -- A data family, with its representation TyCon
\end{code}


\begin{code}
-- Obtain the axiom of a family instance
famInstAxiom :: FamInst -> CoAxiom
famInstAxiom = fi_axiom

famInstTyCon :: FamInst -> TyCon
famInstTyCon = co_ax_tc . fi_axiom

famInstNthBranch :: FamInst -> Int -> FamInstBranch
famInstNthBranch (FamInst { fi_branches = branches }) index
  = ASSERT( 0 <= index && index < (length branches) )
    branches !! index

famInstSingleBranch :: FamInst -> FamInstBranch
famInstSingleBranch (FamInst { fi_branches = [branch] }) = branch
famInstSingleBranch fi = pprPanic "famInstSingleBranch" (ppr fi)

famInstBranchLHS :: FamInstBranch -> [Type]
famInstBranchLHS = fib_lhs

famInstBranchRoughMatch :: FamInstBranch -> [Maybe Name]
famInstBranchRoughMatch = fib_tcs

-- returns True means the famInst will match all applications
-- returning False gives no information
famInstMatchesAny :: FamInst -> Bool
famInstMatchesAny (FamInst { fi_branches = branches })
  = any (all isNothing . fib_tcs) branches

-- Return the representation TyCons introduced by data family instances, if any
famInstsRepTyCons :: [FamInst] -> [TyCon]
famInstsRepTyCons fis = [tc | FamInst { fi_flavor = DataFamilyInst tc } <- fis]

-- Extracts the TyCon for this *data* (or newtype) instance
famInstRepTyCon_maybe :: FamInst -> Maybe TyCon
famInstRepTyCon_maybe fi 
  = case fi_flavor fi of
       DataFamilyInst tycon -> Just tycon
       SynFamilyInst        -> Nothing

dataFamInstRepTyCon :: FamInst -> TyCon
dataFamInstRepTyCon fi 
  = case fi_flavor fi of
       DataFamilyInst tycon -> tycon
       SynFamilyInst        -> pprPanic "dataFamInstRepTyCon" (ppr fi)
\end{code}

\begin{code}
instance NamedThing FamInst where
   getName = coAxiomName . fi_axiom

instance Outputable FamInst where
   ppr = pprFamInst

instance NamedThing FamInstBranch where
   getName = getName . fib_fam_tc

-- Prints the FamInst as a family instance declaration
pprFamInst :: FamInst -> SDoc
pprFamInst (FamInst { fi_branches = brs, fi_flavor = SynFamilyInst
                    , fi_group = True })
  = hang (ptext (sLit "type instance where"))
       2 (vcat (map pprFamInstBranchHdr brs)) 

pprFamInst fi@(FamInst { fi_flavor = flavor, fi_branches = [br]
                       , fi_group = False })
  = pprFamFlavor flavor <+> pp_instance <+> (pprFamInstBranchHdr br)
  where
    -- For *associated* types, say "type T Int = blah" 
    -- For *top level* type instances, say "type instance T Int = blah"
    pp_instance 
      | isTyConAssoc (famInstTyCon fi) = empty
      | otherwise                      = ptext (sLit "instance")

pprFamInst _ = panic "pprFamInst"

pprFamFlavor :: FamFlavor -> SDoc
pprFamFlavor flavor
  = case flavor of
      SynFamilyInst        -> ptext (sLit "type")
      DataFamilyInst tycon
        | isDataTyCon     tycon -> ptext (sLit "data")
        | isNewTyCon      tycon -> ptext (sLit "newtype")
        | isAbstractTyCon tycon -> ptext (sLit "data")
        | otherwise             -> ptext (sLit "WEIRD") <+> ppr tycon

pprFamInstBranchHdr :: FamInstBranch -> SDoc
pprFamInstBranchHdr (FamInstBranch { fib_fam_tc = fam_tc, fib_lhs = tys })
  = hang (pprTypeApp fam_tc tys)
       2 (ptext (sLit "--") <+> pprDefinedAt (getName fam_tc))

pprFamInstBranch :: FamInstBranch -> SDoc
pprFamInstBranch (FamInstBranch { fib_fam_tc = fam_tc, fib_lhs = lhs
                                , fib_rhs = rhs })
  = pprTypeApp fam_tc lhs <+> equals <+> (ppr rhs)

instance Outputable FamInstBranch where
  ppr = pprFamInstBranch

pprFamInsts :: [FamInst] -> SDoc
pprFamInsts finsts = vcat (map pprFamInst finsts)

pprFamInstBranches :: [FamInstBranch] -> SDoc
pprFamInstBranches branches = vcat (map pprFamInstBranch branches)

-- | Create a branch of a @type@ family instance.
-- This branch must be incorporated into a full @FamInst@ with
-- @mkSynFamInst@ to be useful.
mkSynFamInstBranch :: TyCon   -- ^ family tycon
                   -> [TyVar] -- ^ bound variables
                   -> [Type]  -- ^ LHS type patterns
                   -> Type    -- ^ RHS type
                   -> (FamInstBranch, CoAxBranch)
mkSynFamInstBranch fam_tc tvs lhs_tys rhs_ty
  = ( FamInstBranch { fib_fam_tc = fam_tc
                    , fib_tvs    = mkVarSet tvs
                    , fib_lhs    = lhs_tys
                    , fib_rhs    = rhs_ty
                    , fib_tcs    = mb_tcs }
    , CoAxBranch { cab_tvs = tvs
                 , cab_lhs = lhs_tys
                 , cab_rhs = rhs_ty })
  where
    mb_tcs = roughMatchTcs lhs_tys

-- | Create a coercion identifying a @type@ family instance.
-- It has the form @Co tvs :: F ts ~ R@, where @Co@ is 
-- the coercion constructor built here, @F@ the family tycon and @R@ the
-- right-hand side of the type family instance.
mkSynFamInst :: Name            -- ^ Unique name for the coercion tycon
             -> TyCon           -- ^ Family tycon (@F@)
             -> [(FamInstBranch, CoAxBranch)] -- ^ the branches of this FamInst
             -> FamInst
mkSynFamInst name fam_tc branches
  = ASSERT( length branches >= 1 )
    ASSERT( fam_tc == (fib_fam_tc $ fst $ head branches) )
    FamInst { fi_fam      = tyConName fam_tc
            , fi_flavor   = SynFamilyInst
            , fi_branches = fst $ unzip branches
            , fi_group    = True -- TODO (RAE): fix this
            , fi_axiom    = axiom }
  where
    axiom = CoAxiom { co_ax_unique   = nameUnique name
                    , co_ax_name     = name
                    , co_ax_arity    =
                        length (famInstBranchLHS $ fst $ head branches)
                    , co_ax_tc       = fam_tc
                    , co_ax_implicit = False
                    , co_ax_branches = snd $ unzip branches }

-- | Create a coercion identifying a @type@ family instance, but with only
-- one equation (branch).
mkSingleSynFamInst :: Name        -- ^ Unique name for the coercion tycon
                   -> [TyVar]     -- ^ Type parameters of the coercion (@tvs@)
                   -> TyCon       -- ^ Family tycon (@F@)
                   -> [Type]      -- ^ Type instance (@ts@)
                   -> Type        -- ^ right-hand side
                   -> FamInst
-- See note [Single FamInsts]
mkSingleSynFamInst name tvs fam_tc inst_tys rep_ty
  = FamInst { fi_fam      = tyConName fam_tc
            , fi_flavor   = SynFamilyInst
            , fi_branches = [branch]
            , fi_group    = False
            , fi_axiom    = axiom }
  where
    branch = FamInstBranch { fib_fam_tc = fam_tc
                           , fib_tvs    = mkVarSet tvs
                           , fib_lhs    = inst_tys
                           , fib_rhs    = rep_ty
                           , fib_tcs    = roughMatchTcs inst_tys }
    axiom = CoAxiom { co_ax_unique   = nameUnique name
                    , co_ax_name     = name
                    , co_ax_arity    = length inst_tys
                    , co_ax_tc       = fam_tc
                    , co_ax_implicit = False
                    , co_ax_branches = [axBranch] }
    axBranch = CoAxBranch { cab_tvs = tvs
                          , cab_lhs = inst_tys
                          , cab_rhs = rep_ty }
    
-- | Create a coercion identifying a @data@ or @newtype@ representation type
-- and its family instance.  It has the form @Co tvs :: F ts ~ R tvs@,
-- where @Co@ is the coercion constructor built here, @F@ the family tycon
-- and @R@ the (derived) representation tycon.
mkDataFamInst :: Name         -- ^ Unique name for the coercion tycon
              -> [TyVar]      -- ^ Type parameters of the coercion (@tvs@)
              -> TyCon        -- ^ Family tycon (@F@)
              -> [Type]       -- ^ Type instance (@ts@)
              -> TyCon        -- ^ Representation tycon (@R@)
              -> FamInst
mkDataFamInst name tvs fam_tc inst_tys rep_tc
  = FamInst { fi_fam      = tyConName fam_tc
            , fi_flavor   = DataFamilyInst rep_tc
            , fi_group    = True -- TODO (RAE): fix this
            , fi_branches = [branch]
            , fi_axiom    = axiom }
  where
    rhs = mkTyConApp rep_tc (mkTyVarTys tvs)

    branch = FamInstBranch { fib_fam_tc = fam_tc
                           , fib_tvs    = mkVarSet tvs
                           , fib_lhs    = inst_tys
                           , fib_rhs    = rhs
                           , fib_tcs    = roughMatchTcs inst_tys }

    axiom = CoAxiom { co_ax_unique   = nameUnique name
                    , co_ax_name     = name
                    , co_ax_arity    = length inst_tys
                    , co_ax_tc       = fam_tc
                    , co_ax_branches = [axBranch]
                    , co_ax_implicit = False }

    axBranch = CoAxBranch { cab_tvs = tvs
                          , cab_lhs = inst_tys
                          , cab_rhs = rhs }

-- Make a family instance representation from the information found in an
-- interface file.  In particular, we get the rough match info from the iface
-- (instead of computing it here).
mkImportedFamInst :: Name               -- Name of the family
                  -> [[Maybe Name]]     -- Rough match info, per branch
                  -> CoAxiom            -- Axiom introduced
                  -> FamInst            -- Resulting family instance
mkImportedFamInst fam roughs axiom@(CoAxiom { co_ax_branches = axBranches })
  = ASSERT( fam == tyConName fam_tc )
    FamInst {
      fi_fam      = fam,
      fi_axiom    = axiom,
      fi_flavor   = flavor,
      fi_group    = (length branches /= 1), -- TODO (RAE): Fix this
      fi_branches = branches }
  where
     fam_tc = coAxiomTyCon axiom

     branches = zipWith mk_fam_inst_branch axBranches roughs

     mk_fam_inst_branch (CoAxBranch { cab_tvs = tvs
                                    , cab_lhs = lhs
                                    , cab_rhs = rhs }) mb_tcs
       = FamInstBranch { fib_fam_tc = fam_tc
                       , fib_tvs    = mkVarSet tvs
                       , fib_lhs    = lhs
                       , fib_rhs    = rhs
                       , fib_tcs    = mb_tcs }

         -- Derive the flavor for an imported FamInst rather disgustingly
         -- Maybe we should store it in the IfaceFamInst?
     flavor
       | [CoAxBranch { cab_rhs = rhs }] <- axBranches
       , Just (tc, _) <- splitTyConApp_maybe rhs
       , Just ax' <- tyConFamilyCoercion_maybe tc
       , ax' == axiom
       = DataFamilyInst tc

       | otherwise
       = SynFamilyInst
\end{code}



%************************************************************************
%*									*
		FamInstEnv
%*									*
%************************************************************************

Note [FamInstEnv]
~~~~~~~~~~~~~~~~~~~~~
A FamInstEnv maps a family name to the list of known instances for that family.

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
  = FamIE [FamInst]	-- The instances for a particular family, in any order
  	  Bool 		-- True <=> there is an instance of form T a b c
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

famInstEnvElts :: FamInstEnv -> [FamInst]
famInstEnvElts fi = [elt | FamIE elts _ <- eltsUFM fi, elt <- elts]

familyInstances :: (FamInstEnv, FamInstEnv) -> TyCon -> [FamInst]
familyInstances (pkg_fie, home_fie) fam
  = get home_fie ++ get pkg_fie
  where
    get env = case lookupUFM env fam of
		Just (FamIE insts _) -> insts
		Nothing	             -> []

extendFamInstEnvList :: FamInstEnv -> [FamInst] -> FamInstEnv
extendFamInstEnvList inst_env fis = foldl extendFamInstEnv inst_env fis

extendFamInstEnv :: FamInstEnv -> FamInst -> FamInstEnv
extendFamInstEnv inst_env ins_item@(FamInst {fi_fam = cls_nm})
  = addToUFM_C add inst_env cls_nm (FamIE [ins_item] ins_tyvar)
  where
    add (FamIE items tyvar) _ = FamIE (ins_item:items)
				      (ins_tyvar || tyvar)
    ins_tyvar = famInstMatchesAny ins_item

deleteFromFamInstEnv :: FamInstEnv -> FamInst -> FamInstEnv
deleteFromFamInstEnv inst_env fam_inst@(FamInst {fi_fam = fam_nm})
 = adjustUFM adjust inst_env fam_nm
 where
   adjust :: FamilyInstEnv -> FamilyInstEnv
   adjust (FamIE items tyvars)
     = FamIE (filterOut (identicalFamInst fam_inst) items) tyvars

identicalFamInst :: FamInst -> FamInst -> Bool
-- Same LHS, *and* the instance is defined in the same module
-- Used for overriding in GHCi
identicalFamInst (FamInst { fi_axiom = ax1 }) (FamInst { fi_axiom = ax2 })
  =  nameModule (coAxiomName ax1) == nameModule (coAxiomName ax2)
     && length brs1 == length brs2
     && and (zipWith identical_ax_branch brs1 brs2)
  where brs1 = coAxiomBranches ax1
        brs2 = coAxiomBranches ax2
        identical_ax_branch br1 br2
          = length tvs1 == length tvs2
            && length lhs1 == length lhs2
            && and (zipWith (eqTypeX rn_env) lhs1 lhs2)
          where
            tvs1 = coAxBranchTyVars br1
            tvs2 = coAxBranchTyVars br2
            lhs1 = coAxBranchLHS br1
            lhs2 = coAxBranchLHS br2
            rn_env = rnBndrs2 (mkRnEnv2 emptyInScopeSet) tvs1 tvs2
                       
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
have to go back to all previous FamInstBranchess and check that, under the
substitution induced by the match, other matches are not possible. This is
similar to what happens with class instance selection, when we need to
guarantee that there is only a match and no unifiers. The exact algorithm is
different here because the the potentially-overlapping group is closed.

ALTERNATE APPROACH: As we are processing the branches, we could check if an
instance unifies but does not match. If this happens, there is no possible
match and we can fail right away. This might be more efficient.

Note [Early failure optimisation for instance groups]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
As we're searching through the instances for a match, it is
possible that we find an branch within an instance that matches, but
a previous branch still unifies. In this case, we can abort the
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
possibilities. The fourth one matches, with subst [d |-> e]. We then
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
-- when matching a type family application, we get a FamInst,
-- a 0-based index of the branch that matched, and the list of types
-- the axiom should be applied to
data FamInstMatch = FamInstMatch { fim_instance :: FamInst
                                 , fim_index    :: Int
                                 , fim_tys      :: [Type]
                                 }

instance Outputable FamInstMatch where
  ppr (FamInstMatch { fim_instance = inst
                    , fim_index    = ind
                    , fim_tys      = tys })
    = ptext (sLit "match with") <+> parens (ppr inst)
        <> brackets (ppr ind) <+> ppr tys

lookupFamInstEnv
    :: FamInstEnvs
    -> TyCon -> [Type]		-- What we are looking for
    -> [FamInstMatch]           -- Successful matches
-- Precondition: the tycon is saturated (or over-saturated)

lookupFamInstEnv
  = lookup_fam_inst_env match True
  where
    match seen branch@(FamInstBranch { fib_tvs = tpl_tvs,
                                       fib_lhs = tpl_tys })
          _ match_tys 
      = ASSERT( tyVarsOfTypes match_tys `disjointVarSet` tpl_tvs )
		-- Unification will break badly if the variables overlap
		-- They shouldn't because we allocate separate uniques for them
        case tcMatchTys tpl_tvs tpl_tys match_tys of
          -- success
          Just subst
            | checkUnify seen match_tys subst branch
            -> (Nothing, StopSearching) -- we found an incoherence, so stop searching
            -- see Note [Early failure optimisation for instance groups]

            | otherwise
            -> (Just subst, KeepSearching)

          -- failure; instance not relevant
          Nothing -> (Nothing, KeepSearching) 
    
    -- see Note [Instance checking within groups]
    checkUnify :: [FamInstBranch] -- the previous branches in the instance that matched
               -> [Type]          -- the types in the tyfam application we are matching
               -> TvSubst         -- the subst witnessing the match between those types and...
               -> FamInstBranch   -- ...this FamInstBranch
               -> Bool            -- is there a conflicting unification?
    checkUnify [] _ _ _ = False
    checkUnify ((FamInstBranch { fib_lhs = tpl_tys
                               , fib_rhs = inner_rhs }) : rest)
               match_tys outer_subst
               outer_branch@(FamInstBranch { fib_rhs = outer_rhs })
      = let rest_unify = checkUnify rest match_tys outer_subst outer_branch in
        case tcUnifyTys instanceBindFun tpl_tys match_tys of
          Just inner_subst -> -- see Note [Confluence checking within groups]
            let outer_rhs' = substTy inner_subst $
                             substTy outer_subst outer_rhs
                inner_rhs' = substTy inner_subst inner_rhs in
            not (outer_rhs' `eqType` inner_rhs') || rest_unify
          Nothing -> rest_unify

lookupFamInstEnvConflicts
    :: FamInstEnvs
    -> Bool             -- True <=> we are checking part of a group with other branches
    -> FamInstBranch	-- the putative new instance branch
    -> [FamInstMatch] 	-- Conflicting branches
-- E.g. when we are about to add
--    f : type instance F [a] = a->a
-- we do (lookupFamInstConflicts f [b])
-- to find conflicting matches
--
-- Precondition: the tycon is saturated (or over-saturated)

lookupFamInstEnvConflicts envs grp
                          branch@(FamInstBranch { fib_lhs = tys, fib_rhs = rhs
                                                , fib_fam_tc = tc })
  = lookup_fam_inst_env my_unify False envs tc tys
  where
    my_unify _ (FamInstBranch { fib_tvs = tpl_tvs, fib_lhs = tpl_tys
                              , fib_rhs = tpl_rhs }) old_grp match_tys
       = ASSERT2( tyVarsOfTypes tys `disjointVarSet` tpl_tvs,
		  (ppr branch <+> ppr tys) $$
		  (ppr tpl_tvs <+> ppr tpl_tys) )
		-- Unification will break badly if the variables overlap
		-- They shouldn't because we allocate separate uniques for them
         case tcUnifyTys instanceBindFun tpl_tys match_tys of
	      Just subst
                |  isDataFamilyTyCon tc
                || grp
                || old_grp
                || rhs_conflict tpl_rhs rhs subst
                -> (Just subst, KeepSearching)
                | otherwise -- confluent overlap
                -> (Nothing, KeepSearching)
	      -- irrelevant instance
              Nothing -> (Nothing, KeepSearching)

    -- checks whether two RHSs are distinct, under a unifying substitution
    -- Note [Family instance overlap conflicts]
    rhs_conflict :: Type -> Type -> TvSubst -> Bool
    rhs_conflict rhs1 rhs2 subst 
      = not (rhs1' `eqType` rhs2')
        where
          rhs1' = substTy subst rhs1
          rhs2' = substTy subst rhs2

-- This variant is called when we want to check if the conflict is only in the
-- home environment (see FamInst.addLocalFamInst)
lookupFamInstEnvConflicts' :: FamInstEnv -> Bool -> FamInstBranch -> [FamInstMatch]
lookupFamInstEnvConflicts' env grp fib
  = lookupFamInstEnvConflicts (emptyFamInstEnv, env) grp fib
\end{code}

Note [lookup_fam_inst_env' implementation]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
To reduce code duplication, both lookups during simplification and conflict
checking are routed through lookup_fam_inst_env', which looks for a
matching/unifying branch compared to some target. In the simplification
case, the search is for a match for a target application; in the conflict-
checking case, the search is for a unifier for a putative new instance branch.

The two uses are differentiated by different MatchFuns, which look at a given
branch to see if it is relevant and whether the search should continue. The
the branch is relevant (i.e. matches or unifies), Just <something> is
returned; if the instance is not relevant, Nothing is returned. The MatchFun
also indicates what the search algorithm should do next: it could
KeepSearching or StopSearching.

When to StopSearching? See Note [Early failure optimisation for instance groups]

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
  the neither instance declares an instance group and the right-hand
  sides of the overlapping rules coincide under the overlap substitution.
  For example:
       type instance F a Int = a
       type instance F Int b = b
  These two overlap on (F Int Int) but then both RHSs are Int, 
  so all is well. We require that they are syntactically equal;
  anything else would be difficult to test for at this stage.

\begin{code}
------------------------------------------------------------
data ContSearch = KeepSearching
                | StopSearching

-- Might be a one-way match or a unifier
type MatchFun =  [FamInstBranch]     -- the previous branches in the instance
              -> FamInstBranch       -- the individual branch to check
              -> Bool                -- is this branch a part of a group?
              -> [Type]              -- the types to match against
              -> (Maybe TvSubst, ContSearch)

type OneSidedMatch = Bool     -- Are optimisations that are only valid for
                              -- one sided matches allowed?

lookup_fam_inst_env' 	      -- The worker, local to this module
    :: MatchFun
    -> OneSidedMatch
    -> FamInstEnv
    -> TyCon -> [Type]		-- What we are looking for
    -> [FamInstMatch] 	 
lookup_fam_inst_env' match_fun one_sided ie fam tys
  | not (isFamilyTyCon fam) 
  = []
  | otherwise
	-- Family type applications must be saturated
  = ASSERT2( n_tys >= arity, ppr fam <+> ppr tys )
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
		   Nothing -> []	-- No instances for this class
		   Just (FamIE insts has_tv_insts)
		       -- Short cut for common case:
		       --   The thing we are looking up is of form (C a
		       --   b c), and the FamIE has no instances of
		       --   that form, so don't bother to search 
		     | all_tvs && not has_tv_insts -> []
		     | otherwise                   -> find insts

    --------------
    find :: [FamInst] -> [FamInstMatch]
    find [] = []
    find (inst@(FamInst { fi_branches = branches }) : rest)
      = case findBranch [] branches inst 0 of
          (Just match, StopSearching) -> [match]
          (Just match, KeepSearching) -> match : find rest
          (Nothing,    StopSearching) -> []
          (Nothing,    KeepSearching) -> find rest

    findBranch :: [FamInstBranch] -- the branches that have already been checked
               -> [FamInstBranch] -- still looking through these
               -> FamInst         -- the instance we're looking through
               -> Int             -- the index of the next branch
               -> (Maybe FamInstMatch, ContSearch)
    findBranch _ [] _ _ = (Nothing, KeepSearching)
    findBranch seen (branch@(FamInstBranch { fib_tcs = mb_tcs }) : rest)
                    inst@(FamInst { fi_axiom = axiom, fi_group = group }) ind
      | instanceCantMatch rough_tcs mb_tcs
      = findBranch seen rest inst (ind+1) -- branch won't unify later; ignore
      | otherwise
      = case match_fun seen branch group match_tys of
          (Nothing, KeepSearching) -> findBranch (branch : seen) rest inst (ind+1)
          (Nothing, StopSearching) -> (Nothing, StopSearching)
          (Just subst, cont)       -> (Just match, cont)
            where match = FamInstMatch { fim_instance = inst
                                       , fim_index    = ind
                                       , fim_tys      = tys }
                  axBranch = coAxiomNthBranch axiom ind
                  tys = add_extra_tys $
                        substTyVars subst (coAxBranchTyVars axBranch)

lookup_fam_inst_env 	      -- The worker, local to this module
    :: MatchFun
    -> OneSidedMatch
    -> FamInstEnvs
    -> TyCon -> [Type]		-- What we are looking for
    -> [FamInstMatch]           -- What was found

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

\begin{code}

-- checks if one LHS is dominated by a list of other branches
-- in other words, if an application would match the first LHS, it is guaranteed
-- to match at least one of the others. The RHSs are ignored.
-- This algorithm is conservative:
--   True -> the LHS is definitely covered by the others
--   False -> no information
-- It is currently (Oct 2012) used only for generating errors for
-- inaccessible branches. If these errors go unreported, no harm done.
isDominatedBy :: [Type] -> [FamInstBranch] -> Bool
isDominatedBy lhs branches
  = or $ map match branches
    where
      match (FamInstBranch { fib_tvs = tvs, fib_lhs = tys })
        = isJust $ tcMatchTys tvs tys lhs

\end{code}


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
          else let nt_co = mkSingletonAxInstCo (newTyConCo tc) tys
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
                  , fim_index    = fam_ind
                  , fim_tys      = inst_tys }] <- lookupFamInstEnv env tc ntys 
  = let    -- A matching family instance exists
        ax              = famInstAxiom fam_inst
        co              = mkAxInstCo  ax fam_ind inst_tys
        rhs             = mkAxInstRHS ax fam_ind inst_tys
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
