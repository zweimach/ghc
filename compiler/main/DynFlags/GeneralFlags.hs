module DynFlags.GeneralFlags where

import DynFlags.Parser

data GeneralFlag
-- See Note [Updating flag description in the User's Guide]

   = Opt_DumpToFile                     -- ^ Append dump output to files instead of stdout.
   | Opt_D_faststring_stats
   | Opt_D_dump_minimal_imports
   | Opt_DoCoreLinting
   | Opt_DoStgLinting
   | Opt_DoCmmLinting
   | Opt_DoAsmLinting
   | Opt_DoAnnotationLinting
   | Opt_NoLlvmMangler                 -- hidden flag

   | Opt_WarnIsError                    -- -Werror; makes warnings fatal
   | Opt_ShowWarnGroups                 -- Show the group a warning belongs to
   | Opt_HideSourcePaths                -- Hide module source/object paths

   | Opt_PrintExplicitForalls
   | Opt_PrintExplicitKinds
   | Opt_PrintExplicitCoercions
   | Opt_PrintExplicitRuntimeReps
   | Opt_PrintEqualityRelations
   | Opt_PrintUnicodeSyntax
   | Opt_PrintExpandedSynonyms
   | Opt_PrintPotentialInstances
   | Opt_PrintTypecheckerElaboration

   -- optimisation opts
   | Opt_CallArity
   | Opt_Strictness
   | Opt_LateDmdAnal
   | Opt_KillAbsence
   | Opt_KillOneShot
   | Opt_FullLaziness
   | Opt_FloatIn
   | Opt_Specialise
   | Opt_SpecialiseAggressively
   | Opt_CrossModuleSpecialise
   | Opt_StaticArgumentTransformation
   | Opt_CSE
   | Opt_StgCSE
   | Opt_LiberateCase
   | Opt_SpecConstr
   | Opt_SpecConstrKeen
   | Opt_DoLambdaEtaExpansion
   | Opt_IgnoreAsserts
   | Opt_DoEtaReduction
   | Opt_CaseMerge
   | Opt_CaseFolding                    -- Constant folding through case-expressions
   | Opt_UnboxStrictFields
   | Opt_UnboxSmallStrictFields
   | Opt_DictsCheap
   | Opt_EnableRewriteRules             -- Apply rewrite rules during simplification
   | Opt_Vectorise
   | Opt_VectorisationAvoidance
   | Opt_RegsGraph                      -- do graph coloring register allocation
   | Opt_RegsIterative                  -- do iterative coalescing graph coloring register allocation
   | Opt_PedanticBottoms                -- Be picky about how we treat bottom
   | Opt_LlvmTBAA                       -- Use LLVM TBAA infastructure for improving AA (hidden flag)
   | Opt_LlvmPassVectorsInRegisters     -- Pass SIMD vectors in registers (requires a patched LLVM) (hidden flag)
   | Opt_LlvmFillUndefWithGarbage       -- Testing for undef bugs (hidden flag)
   | Opt_IrrefutableTuples
   | Opt_CmmSink
   | Opt_CmmElimCommonBlocks
   | Opt_OmitYields
   | Opt_FunToThunk               -- allow WwLib.mkWorkerArgs to remove all value lambdas
   | Opt_DictsStrict                     -- be strict in argument dictionaries
   | Opt_DmdTxDictSel              -- use a special demand transformer for dictionary selectors
   | Opt_Loopification                  -- See Note [Self-recursive tail calls]
   | Opt_CprAnal
   | Opt_WorkerWrapper
   | Opt_SolveConstantDicts

   -- Interface files
   | Opt_IgnoreInterfacePragmas
   | Opt_OmitInterfacePragmas
   | Opt_ExposeAllUnfoldings
   | Opt_WriteInterface -- forces .hi files to be written even with -fno-code

   -- profiling opts
   | Opt_AutoSccsOnIndividualCafs
   | Opt_ProfCountEntries

   -- misc opts
   | Opt_Pp
   | Opt_ForceRecomp
   | Opt_ExcessPrecision
   | Opt_EagerBlackHoling
   | Opt_NoHsMain
   | Opt_SplitObjs
   | Opt_SplitSections
   | Opt_StgStats
   | Opt_HideAllPackages
   | Opt_HideAllPluginPackages
   | Opt_PrintBindResult
   | Opt_Haddock
   | Opt_HaddockOptions
   | Opt_BreakOnException
   | Opt_BreakOnError
   | Opt_PrintEvldWithShow
   | Opt_PrintBindContents
   | Opt_GenManifest
   | Opt_EmbedManifest
   | Opt_SharedImplib
   | Opt_BuildingCabalPackage
   | Opt_IgnoreDotGhci
   | Opt_GhciSandbox
   | Opt_GhciHistory
   | Opt_LocalGhciHistory
   | Opt_HelpfulErrors
   | Opt_DeferTypeErrors
   | Opt_DeferTypedHoles
   | Opt_DeferOutOfScopeVariables
   | Opt_PIC
   | Opt_SccProfilingOn
   | Opt_Ticky
   | Opt_Ticky_Allocd
   | Opt_Ticky_LNE
   | Opt_Ticky_Dyn_Thunk
   | Opt_RPath
   | Opt_RelativeDynlibPaths
   | Opt_Hpc
   | Opt_FlatCache
   | Opt_ExternalInterpreter
   | Opt_OptimalApplicativeDo
   | Opt_VersionMacros
   | Opt_WholeArchiveHsLibs

   -- PreInlining is on by default. The option is there just to see how
   -- bad things get if you turn it off!
   | Opt_SimplPreInlining

   -- output style opts
   | Opt_ErrorSpans -- Include full span info in error messages,
                    -- instead of just the start position.
   | Opt_DiagnosticsShowCaret -- Show snippets of offending code
   | Opt_PprCaseAsLet
   | Opt_PprShowTicks
   | Opt_ShowHoleConstraints

   -- Suppress all coercions, them replacing with '...'
   | Opt_SuppressCoercions
   | Opt_SuppressVarKinds
   -- Suppress module id prefixes on variables.
   | Opt_SuppressModulePrefixes
   -- Suppress type applications.
   | Opt_SuppressTypeApplications
   -- Suppress info such as arity and unfoldings on identifiers.
   | Opt_SuppressIdInfo
   -- Suppress separate type signatures in core, but leave types on
   -- lambda bound vars
   | Opt_SuppressUnfoldings
   -- Suppress the details of even stable unfoldings
   | Opt_SuppressTypeSignatures
   -- Suppress unique ids on variables.
   -- Except for uniques, as some simplifier phases introduce new
   -- variables that have otherwise identical names.
   | Opt_SuppressUniques
   | Opt_SuppressTicks     -- Replaces Opt_PprShowTicks

   -- temporary flags
   | Opt_AutoLinkPackages
   | Opt_ImplicitImportQualified

   -- keeping stuff
   | Opt_KeepHiDiffs
   | Opt_KeepHcFiles
   | Opt_KeepSFiles
   | Opt_KeepTmpFiles
   | Opt_KeepRawTokenStream
   | Opt_KeepLlvmFiles
   | Opt_KeepHiFiles
   | Opt_KeepOFiles

   | Opt_BuildDynamicToo

   -- safe haskell flags
   | Opt_DistrustAllPackages
   | Opt_PackageTrust

   | Opt_G_NoStateHack
   | Opt_G_NoOptCoercion
   deriving (Eq, Show, Enum)

-- | These @-d\<blah\>@ flags can all be reversed with @-dno-\<blah\>@
dFlagsDeps :: [(Deprecation, FlagSpec GeneralFlag)]
dFlagsDeps = [
-- See Note [Updating flag description in the User's Guide]
-- See Note [Supporting CLI completion]
-- Please keep the list of flags below sorted alphabetically
  flagSpec "ppr-case-as-let"            Opt_PprCaseAsLet,
  depFlagSpec' "ppr-ticks"              Opt_PprShowTicks
     (\turn_on -> useInstead "suppress-ticks" (not turn_on)),
  flagSpec "suppress-ticks"             Opt_SuppressTicks,
  flagSpec "suppress-coercions"         Opt_SuppressCoercions,
  flagSpec "suppress-idinfo"            Opt_SuppressIdInfo,
  flagSpec "suppress-unfoldings"        Opt_SuppressUnfoldings,
  flagSpec "suppress-module-prefixes"   Opt_SuppressModulePrefixes,
  flagSpec "suppress-type-applications" Opt_SuppressTypeApplications,
  flagSpec "suppress-type-signatures"   Opt_SuppressTypeSignatures,
  flagSpec "suppress-uniques"           Opt_SuppressUniques,
  flagSpec "suppress-var-kinds"         Opt_SuppressVarKinds]

useInstead :: String -> TurnOnFlag -> String
useInstead flag turn_on
  = "Use -f" ++ no ++ flag ++ " instead"
  where
    no = if turn_on then "" else "no-"
