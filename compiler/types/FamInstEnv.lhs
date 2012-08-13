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

        FamInstMatch(..), LookupFamInstResult(..), FamIncoherence(..),
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

\begin{code}
data FamInstMatch 
  = FamInstMatch { fim_instance :: FamInst -- the matching FamInst
                 , fim_tys      :: [Type]  -- the substituted types
                                           -- See Note [Over-saturated matches]
                 , fim_group    :: FamInstGroup -- the group to which the match belongs
                   -- INVARIANT: fim_instance `elem` (famInstGroupInsts fim_group)
                 }

-- It is possible that the lookup results in finding an incoherent instance
-- group. (See note [Instance checking within groups].) This type packages
-- up the information about the incoherence to allow for an informative error
-- message.
data FamIncoherence
  = FamIncoherence { faminc_match :: FamInst   -- the instance that matched
                   , faminc_unify :: FamInst } -- the (preceding) instance that unified

-- There are three posibilities from a family instance lookup:
-- 1) Success
-- 2) Failure
-- 3) Encountering an incoherent instance group
data LookupFamInstResult = FamInstSuccess FamInstMatch       -- we found a match
                         | FamInstFailure                    -- no match, keep searching
                         | FamInstIncoherent FamIncoherence  -- match impossible
                              -- see note [Early failure optimisation for instance groups]

-- this is only ever used in debugging output, never in user-intended errors
pprFamIncoherence :: FamIncoherence -> SDoc
pprFamIncoherence (FamIncoherence { faminc_match = match, faminc_unify = unify })
  = hang (ptext (sLit "incoherence detected:"))
       2 (ppr match $$ ppr unify)

-- similarly used only in debugging
pprFamInstMatch :: FamInstMatch -> SDoc
pprFamInstMatch (FamInstMatch { fim_instance = inst
                              , fim_tys      = tys
                              , fim_group    = group })
  = hang (ptext (sLit "FamInstMatch {"))
       2 (vcat [ptext (sLit "fim_instance") <+> equals <+> ppr inst,
                ptext (sLit "fim_tys     ") <+> equals <+> ppr tys,
                ptext (sLit "fim_group   ") <+> equals <+> ppr group <+> ptext (sLit "}")])

instance Outputable FamIncoherence where
  ppr = pprFamIncoherence

instance Outputable FamInstMatch where
  ppr = pprFamInstMatch

lookupFamInstEnv
    :: FamInstEnvs
    -> TyCon -> [Type]		            -- What we are looking for
    -> Either FamIncoherence [FamInstMatch] -- Successful matches
-- Precondition: the tycon is saturated (or over-saturated)

lookupFamInstEnv
   = lookup_fam_inst_env match OneSidedMatch
   where
     match _ tpl_tvs tpl_tys tys = (tcMatchTys tpl_tvs tpl_tys tys, True)

lookupFamInstEnvConflicts
    :: FamInstEnvs
    -> Bool             -- is this a data family?
    -> TyCon            -- family tycon
    -> [FamInst]        -- the instances that came before the current one
                        -- in the group
    -> FamInst		-- Putative new instance
    -> [TyVar]		-- Unique tyvars, matching arity of FamInst
    -> [FamInstMatch] 	-- Conflicting matches
-- E.g. when we are about to add
--    f : type instance F [a] = a->a
-- we do (lookupFamInstConflicts f [b])
-- to find conflicting matches
-- The skolem tyvars are needed because we don't have a 
-- unique supply to hand
--
-- Precondition: the tycon is saturated (or over-saturated)

lookupFamInstEnvConflicts envs data_fam fam prev_insts fam_inst skol_tvs
  = case lookup_fam_inst_env my_unify (UnificationForConflict prev_insts)
                             envs fam tys1 of
      Left incoh -> pprPanic "lookupFamInstEnvConflicts" (ppr incoh)
      Right matches -> matches
  where
    inst_axiom = famInstAxiom fam_inst
    tys        = famInstTys fam_inst
    skol_tys   = mkTyVarTys skol_tvs
    tys1       = substTys (zipTopTvSubst (coAxiomTyVars inst_axiom) skol_tys) tys
        -- In example above,   fam tys' = F [b]   

    my_unify old_fam_inst tpl_tvs tpl_tys match_tys
       = ASSERT2( tyVarsOfTypes tys1 `disjointVarSet` tpl_tvs,
		  (ppr fam_inst <+> ppr tys1) $$
		  (ppr tpl_tvs <+> ppr tpl_tys) )
		-- Unification will break badly if the variables overlap
		-- They shouldn't because we allocate separate uniques for them
         case tcUnifyTys instanceBindFun tpl_tys match_tys of
	      Just subst -> if conflicting old_fam_inst subst
                             then (Just subst, True)
                             else (Nothing, False)
	      _other	 -> (Nothing, True)

      -- Note [Family instance overlap conflicts]
    conflicting old_fam_inst subst 
      | data_fam  = True
      | otherwise = not (old_rhs `eqType` new_rhs)
      where
        old_axiom = famInstAxiom old_fam_inst
        old_tvs   = coAxiomTyVars old_axiom
        old_rhs   = mkAxInstRHS old_axiom  (substTyVars subst old_tvs)
        new_rhs   = mkAxInstRHS inst_axiom (substTyVars subst skol_tvs)

-- This variant is called when we want to check if the conflict is only in the
-- home environment (see FamInst.addLocalFamInst)
lookupFamInstEnvConflicts' :: FamInstEnv -> Bool -> TyCon
                           -> [FamInst] -> FamInst -> [TyVar] -> [FamInstMatch]
lookupFamInstEnvConflicts' env
  = lookupFamInstEnvConflicts (emptyFamInstEnv, env)
\end{code}

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


While @lookupFamInstEnv@ uses a one-way match, the next function
@lookupFamInstEnvConflicts@ uses two-way matching (ie, unification).  This is
needed to check for overlapping instances.

For class instances, these two variants of lookup are combined into one
function (cf, @InstEnv@).  We don't do that for family instances as the
results of matching and unification are used in two different contexts.
Moreover, matching is the wildly more frequently used operation in the case of
indexed synonyms and we don't want to slow that down by needless unification.

Both matching lookups and conflict lookups boil down to same worker function,
lookup_fam_inst_env', which uses a function argument to differentiate between
matching and unifying. When unifying, the my_unify function (defined in the
'where' clause of lookupFamInstEnvConflicts) would like to indicate "no match"
when there is a match but the RHSs are confluent, as confluent RHSs do not
indicate a conflict. However, when checking in an instance group, a "no match"
says to keep looking later in the instance group. That behavior is wrong.
For example,

type family F a b
type instance where
  F a a = Char
  F a b = Double
type instance F Int Int = Char

This code contains no conflicts. But, if my_unify simply returns that
'F a a = Char' and 'F Int Int = Char' are not a match (because they do
not conflict), then lookup_fam_inst_env' continues to search through
the instance group, finding 'F a b = Double'. This LHS unifies with
'F Int Int' but the RHS does not, and an erroneous conflict is reported.

To get around this, the matching functions passed into lookup_fam_inst_env'
return a pair of a Maybe TvSubst (the substitution, if there is a match) and
a Boolean flag. The flag says whether the search within an instance group
should continue in the case where a match was not found. (When a match was found,
we know always to stop the search.) Thus, if the return value is (Just _, b)
the value of b is ignored.

Conversely, consider conflict checking in the reverse order, with the
singleton instance 'F Int Int' first. We accept 'F a a' as without conflicts
wthout a problem. However, 'F a b' gives trouble: it unifies with 'F Int Int'.
The solution here is that we have to ignore any outside instance that
unifies with any of the instances previous to the one in question but in
the same instance group. So, in this case, we wish to ignore the 'F Int Int'
instance in the context when checking 'F a b' because 'F a a' unifies with
'F Int Int'. This check is accomplished using the LookupType datatype below.

\begin{code}
------------------------------------------------------------
-- Might be a one-way match or a unifier
type MatchFun =  FamInst		-- The FamInst template
     	      -> TyVarSet -> [Type]	--   fi_tvs, fi_tys of that FamInst
	      -> [Type]			-- Target to match against
	      -> ( Maybe TvSubst   -- unifying substitution
                 , Bool )          -- if no subst found, keep searching within this group?
                                   -- see Note [Family instance overlap conflicts]

-- informs why we are doing a lookup. See Note [Family instance overlap conflicts]
data LookupType = OneSidedMatch -- trying to match a type (for example, in simplification)
                | UnificationForConflict [FamInst]
                    -- looking for conflicts. The [FamInst] are the instances in the
                    -- group before the one being checked. This is necessary because
                    -- if a potentially conficting instance matches wth any of these,
                    -- it is irrelevant if it matches with the instance in question.

lookup_fam_inst_env' 	      -- The worker, local to this module
    :: MatchFun
    -> LookupType
    -> FamInstEnv
    -> TyCon -> [Type]		-- What we are looking for
    -> Either FamIncoherence [FamInstMatch] 
lookup_fam_inst_env' match_fun lookup_type ie fam tys
  | not (isFamilyTyCon fam) 
  = Right []
  | otherwise
  = ASSERT2( n_tys >= arity, ppr fam <+> ppr tys )	-- Family type applications must be saturated
    lookup ie
  where
    one_sided | OneSidedMatch <- lookup_type = True
              | otherwise                    = False

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
		   Nothing -> Right []	-- No instances for this class
		   Just (FamIE groups has_tv_insts)
		       -- Short cut for common case:
		       --   The thing we are looking up is of form (C a
		       --   b c), and the FamIE has no instances of
		       --   that form, so don't bother to search 
		     | all_tvs && not has_tv_insts -> Right []
		     | otherwise                   -> findGroup groups

    --------------
    findGroup :: [FamInstGroup] -> Either FamIncoherence [FamInstMatch]
    findGroup [] = Right []
    findGroup (group@(FamInstGroup { fig_fis = fam_insts }) : rest)
      = case find group fam_insts of
          FamInstSuccess match ->
            case findGroup rest of
              Left incoherence -> pprPanic "lookup_fam_inst_env'"
                                           (ppr match $$ ppr incoherence)
              Right more_matches -> Right $ match : more_matches
          FamInstFailure -> findGroup rest
          FamInstIncoherent incoh -> Left incoh

    find group = find_and_check group []

    -- See note [Instance checking within groups]
    find_and_check :: FamInstGroup -- the group in which we are checking
                   -> [FamInst]    -- the FamInsts that have already been checked
                   -> [FamInst]    -- still looking through these
                   -> LookupFamInstResult
    find_and_check _ _ [] = FamInstFailure
    find_and_check group seen
                   (item@(FamInst { fi_tcs = mb_tcs, fi_tvs = tpl_tvs, 
                                    fi_tys = tpl_tys, fi_axiom = axiom }) : rest)
	-- Fast check for no match, uses the "rough match" fields
      | instanceCantMatch rough_tcs mb_tcs
      = find_and_check group seen rest -- just discard this one. It won't unify later.

        -- Proper check
      | otherwise
      = case match_fun item tpl_tvs tpl_tys match_tys of
          -- success
          (Just subst, _) ->
            let substed_tys = substTyVars subst (coAxiomTyVars axiom) in
            case checkUnify seen tpl_tys of
              Nothing -> FamInstSuccess (FamInstMatch
                           { fim_instance = item
                           , fim_tys      = add_extra_tys $ substed_tys
                           , fim_group    = group  })
              Just fam_inst
                | one_sided
                -> FamInstIncoherent (FamIncoherence { faminc_match = item
                                                     , faminc_unify = fam_inst })
                | otherwise
                -> FamInstFailure -- we don't want to abort the search when
                                  -- looking for conflicts
          -- fail and continue
          (Nothing, True) -> find_and_check group (item : seen) rest
          
          -- fail and stop
          (Nothing, False) -> FamInstFailure

    checkUnify :: [FamInst]     -- previous FamInsts in the group we're searching through
               -> [Type]        -- the matching substitution applied to the tyvars
                                -- the matching instance
               -> Maybe FamInst -- the FamInst that unifies, or Nothing
    checkUnify seen substed_tys
      | UnificationForConflict other_insts <- lookup_type
      = do_check other_insts substed_tys
      | otherwise
      = do_check seen match_tys

    -- TODO (RAE): Allow confluent overlaps.
    do_check [] _ = Nothing
    do_check (fam_inst@(FamInst { fi_tys = tpl_tys }) : rest) tys
      | Just _ <- tcUnifyTys instanceBindFun tpl_tys tys
      = Just fam_inst
      | otherwise
      = do_check rest tys

-- Precondition: the tycon is saturated (or over-saturated)

lookup_fam_inst_env 	      -- The worker, local to this module
    :: MatchFun
    -> LookupType
    -> FamInstEnvs
    -> TyCon -> [Type]		-- What we are looking for
    -> Either FamIncoherence [FamInstMatch] -- failure message or Successful matches

-- Precondition: the tycon is saturated (or over-saturated)

lookup_fam_inst_env match_fun one_sided (pkg_ie, home_ie) fam tys = 
    lookup_fam_inst_env' match_fun one_sided home_ie fam tys `append`
    lookup_fam_inst_env' match_fun one_sided pkg_ie  fam tys
  where append x@(Left _) (Right []) = x
        append (Right []) x@(Left _) = x
        append (Right l1) (Right l2) = Right (l1 ++ l2)
        append x y                   = pprPanic "lookup_fam_inst_env" (ppr x $$ ppr y)
                    -- there should never be a successful match in one environment
                    -- and an incoherence in the other

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
  , Right [FamInstMatch { fim_instance = fam_inst
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
