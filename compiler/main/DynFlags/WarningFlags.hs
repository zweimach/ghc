-- | Warning flags
module DynFlags.WarningFlags where

import CmdLineParser
import DynFlags.Type
import DynFlags.Parser
import DynFlags.GeneralFlags

import Control.Monad
import Data.Maybe
import Data.List
import Data.Ord (comparing)

data WarningFlag =
-- See Note [Updating flag description in the User's Guide]
     Opt_WarnDuplicateExports
   | Opt_WarnDuplicateConstraints
   | Opt_WarnRedundantConstraints
   | Opt_WarnHiShadows
   | Opt_WarnImplicitPrelude
   | Opt_WarnIncompletePatterns
   | Opt_WarnIncompleteUniPatterns
   | Opt_WarnIncompletePatternsRecUpd
   | Opt_WarnOverflowedLiterals
   | Opt_WarnEmptyEnumerations
   | Opt_WarnMissingFields
   | Opt_WarnMissingImportList
   | Opt_WarnMissingMethods
   | Opt_WarnMissingSignatures
   | Opt_WarnMissingLocalSignatures
   | Opt_WarnNameShadowing
   | Opt_WarnOverlappingPatterns
   | Opt_WarnTypeDefaults
   | Opt_WarnMonomorphism
   | Opt_WarnUnusedTopBinds
   | Opt_WarnUnusedLocalBinds
   | Opt_WarnUnusedPatternBinds
   | Opt_WarnUnusedImports
   | Opt_WarnUnusedMatches
   | Opt_WarnUnusedTypePatterns
   | Opt_WarnUnusedForalls
   | Opt_WarnWarningsDeprecations
   | Opt_WarnDeprecatedFlags
   | Opt_WarnAMP -- Introduced in GHC 7.8, obsolete since 7.10
   | Opt_WarnMissingMonadFailInstances -- since 8.0
   | Opt_WarnSemigroup -- since 8.0
   | Opt_WarnDodgyExports
   | Opt_WarnDodgyImports
   | Opt_WarnOrphans
   | Opt_WarnAutoOrphans
   | Opt_WarnIdentities
   | Opt_WarnTabs
   | Opt_WarnUnrecognisedPragmas
   | Opt_WarnDodgyForeignImports
   | Opt_WarnUnusedDoBind
   | Opt_WarnWrongDoBind
   | Opt_WarnAlternativeLayoutRuleTransitional
   | Opt_WarnUnsafe
   | Opt_WarnSafe
   | Opt_WarnTrustworthySafe
   | Opt_WarnMissedSpecs
   | Opt_WarnAllMissedSpecs
   | Opt_WarnUnsupportedCallingConventions
   | Opt_WarnUnsupportedLlvmVersion
   | Opt_WarnInlineRuleShadowing
   | Opt_WarnTypedHoles
   | Opt_WarnPartialTypeSignatures
   | Opt_WarnMissingExportedSignatures
   | Opt_WarnUntickedPromotedConstructors
   | Opt_WarnDerivingTypeable
   | Opt_WarnDeferredTypeErrors
   | Opt_WarnDeferredOutOfScopeVariables
   | Opt_WarnNonCanonicalMonadInstances   -- since 8.0
   | Opt_WarnNonCanonicalMonadFailInstances -- since 8.0
   | Opt_WarnNonCanonicalMonoidInstances  -- since 8.0
   | Opt_WarnMissingPatternSynonymSignatures -- since 8.0
   | Opt_WarnUnrecognisedWarningFlags     -- since 8.0
   | Opt_WarnSimplifiableClassConstraints -- Since 8.2
   | Opt_WarnCPPUndef                     -- Since 8.2
   | Opt_WarnUnbangedStrictPatterns       -- Since 8.2
   | Opt_WarnMissingHomeModules           -- Since 8.2
   deriving (Eq, Show, Enum)

-- | Find the 'FlagSpec' for a 'WarningFlag'.
flagSpecOf :: WarningFlag -> Maybe (FlagSpec WarningFlag)
flagSpecOf flag = listToMaybe $ filter check wWarningFlags
  where
    check fs = flagSpecFlag fs == flag

-- | These @-W\<blah\>@ flags can all be reversed with @-Wno-\<blah\>@
wWarningFlags :: [FlagSpec WarningFlag]
wWarningFlags = map snd (sortBy (comparing fst) wWarningFlagsDeps)

wWarningFlagsDeps :: [(Deprecation, FlagSpec WarningFlag)]
wWarningFlagsDeps = [
-- See Note [Updating flag description in the User's Guide]
-- See Note [Supporting CLI completion]
-- Please keep the list of flags below sorted alphabetically
  flagSpec "alternative-layout-rule-transitional"
                                      Opt_WarnAlternativeLayoutRuleTransitional,
  depFlagSpec "amp"                      Opt_WarnAMP
    "it has no effect",
  depFlagSpec "auto-orphans"             Opt_WarnAutoOrphans
    "it has no effect",
  flagSpec "cpp-undef"                   Opt_WarnCPPUndef,
  flagSpec "unbanged-strict-patterns"    Opt_WarnUnbangedStrictPatterns,
  flagSpec "deferred-type-errors"        Opt_WarnDeferredTypeErrors,
  flagSpec "deferred-out-of-scope-variables"
                                         Opt_WarnDeferredOutOfScopeVariables,
  flagSpec "deprecations"                Opt_WarnWarningsDeprecations,
  flagSpec "deprecated-flags"            Opt_WarnDeprecatedFlags,
  flagSpec "deriving-typeable"           Opt_WarnDerivingTypeable,
  flagSpec "dodgy-exports"               Opt_WarnDodgyExports,
  flagSpec "dodgy-foreign-imports"       Opt_WarnDodgyForeignImports,
  flagSpec "dodgy-imports"               Opt_WarnDodgyImports,
  flagSpec "empty-enumerations"          Opt_WarnEmptyEnumerations,
  depFlagSpec "duplicate-constraints"    Opt_WarnDuplicateConstraints
    "it is subsumed by -Wredundant-constraints",
  flagSpec "redundant-constraints"       Opt_WarnRedundantConstraints,
  flagSpec "duplicate-exports"           Opt_WarnDuplicateExports,
  flagSpec "hi-shadowing"                Opt_WarnHiShadows,
  flagSpec "implicit-prelude"            Opt_WarnImplicitPrelude,
  flagSpec "incomplete-patterns"         Opt_WarnIncompletePatterns,
  flagSpec "incomplete-record-updates"   Opt_WarnIncompletePatternsRecUpd,
  flagSpec "incomplete-uni-patterns"     Opt_WarnIncompleteUniPatterns,
  flagSpec "inline-rule-shadowing"       Opt_WarnInlineRuleShadowing,
  flagSpec "identities"                  Opt_WarnIdentities,
  flagSpec "missing-fields"              Opt_WarnMissingFields,
  flagSpec "missing-import-lists"        Opt_WarnMissingImportList,
  depFlagSpec "missing-local-sigs"       Opt_WarnMissingLocalSignatures
    "it is replaced by -Wmissing-local-signatures",
  flagSpec "missing-local-signatures"    Opt_WarnMissingLocalSignatures,
  flagSpec "missing-methods"             Opt_WarnMissingMethods,
  flagSpec "missing-monadfail-instances" Opt_WarnMissingMonadFailInstances,
  flagSpec "semigroup"                   Opt_WarnSemigroup,
  flagSpec "missing-signatures"          Opt_WarnMissingSignatures,
  depFlagSpec "missing-exported-sigs"    Opt_WarnMissingExportedSignatures
    "it is replaced by -Wmissing-exported-signatures",
  flagSpec "missing-exported-signatures" Opt_WarnMissingExportedSignatures,
  flagSpec "monomorphism-restriction"    Opt_WarnMonomorphism,
  flagSpec "name-shadowing"              Opt_WarnNameShadowing,
  flagSpec "noncanonical-monad-instances"
                                         Opt_WarnNonCanonicalMonadInstances,
  flagSpec "noncanonical-monadfail-instances"
                                         Opt_WarnNonCanonicalMonadFailInstances,
  flagSpec "noncanonical-monoid-instances"
                                         Opt_WarnNonCanonicalMonoidInstances,
  flagSpec "orphans"                     Opt_WarnOrphans,
  flagSpec "overflowed-literals"         Opt_WarnOverflowedLiterals,
  flagSpec "overlapping-patterns"        Opt_WarnOverlappingPatterns,
  flagSpec "missed-specialisations"      Opt_WarnMissedSpecs,
  flagSpec "missed-specializations"      Opt_WarnMissedSpecs,
  flagSpec "all-missed-specialisations"  Opt_WarnAllMissedSpecs,
  flagSpec "all-missed-specializations"  Opt_WarnAllMissedSpecs,
  flagSpec' "safe"                       Opt_WarnSafe setWarnSafe,
  flagSpec "trustworthy-safe"            Opt_WarnTrustworthySafe,
  flagSpec "tabs"                        Opt_WarnTabs,
  flagSpec "type-defaults"               Opt_WarnTypeDefaults,
  flagSpec "typed-holes"                 Opt_WarnTypedHoles,
  flagSpec "partial-type-signatures"     Opt_WarnPartialTypeSignatures,
  flagSpec "unrecognised-pragmas"        Opt_WarnUnrecognisedPragmas,
  flagSpec' "unsafe"                     Opt_WarnUnsafe setWarnUnsafe,
  flagSpec "unsupported-calling-conventions"
                                         Opt_WarnUnsupportedCallingConventions,
  flagSpec "unsupported-llvm-version"    Opt_WarnUnsupportedLlvmVersion,
  flagSpec "unticked-promoted-constructors"
                                         Opt_WarnUntickedPromotedConstructors,
  flagSpec "unused-do-bind"              Opt_WarnUnusedDoBind,
  flagSpec "unused-foralls"              Opt_WarnUnusedForalls,
  flagSpec "unused-imports"              Opt_WarnUnusedImports,
  flagSpec "unused-local-binds"          Opt_WarnUnusedLocalBinds,
  flagSpec "unused-matches"              Opt_WarnUnusedMatches,
  flagSpec "unused-pattern-binds"        Opt_WarnUnusedPatternBinds,
  flagSpec "unused-top-binds"            Opt_WarnUnusedTopBinds,
  flagSpec "unused-type-patterns"        Opt_WarnUnusedTypePatterns,
  flagSpec "warnings-deprecations"       Opt_WarnWarningsDeprecations,
  flagSpec "wrong-do-bind"               Opt_WarnWrongDoBind,
  flagSpec "missing-pattern-synonym-signatures"
                                    Opt_WarnMissingPatternSynonymSignatures,
  flagSpec "simplifiable-class-constraints" Opt_WarnSimplifiableClassConstraints,
  flagSpec "missing-home-modules"        Opt_WarnMissingHomeModules,
  flagSpec "unrecognised-warning-flags"  Opt_WarnUnrecognisedWarningFlags ]

-- -----------------------------------------------------------------------------
-- Standard sets of warning options

-- Note [Documenting warning flags]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- If you change the list of warning enabled by default
-- please remember to update the User's Guide. The relevant file is:
--
--  * utils/mkUserGuidePart/
--  * docs/users_guide/using-warnings.rst

-- | Warning groups.
--
-- As all warnings are in the Weverything set, it is ignored when
-- displaying to the user which group a warning is in.
warningGroups :: [(String, [WarningFlag])]
warningGroups =
    [ ("compat",       minusWcompatOpts)
    , ("unused-binds", unusedBindsFlags)
    , ("default",      standardWarnings)
    , ("extra",        minusWOpts)
    , ("all",          minusWallOpts)
    , ("everything",   minusWeverythingOpts)
    ]

-- | Warning group hierarchies, where there is an explicit inclusion
-- relation.
--
-- Each inner list is a hierarchy of warning groups, ordered from
-- smallest to largest, where each group is a superset of the one
-- before it.
--
-- Separating this from 'warningGroups' allows for multiple
-- hierarchies with no inherent relation to be defined.
--
-- The special-case Weverything group is not included.
warningHierarchies :: [[String]]
warningHierarchies = hierarchies ++ map (:[]) rest
  where
    hierarchies = [["default", "extra", "all"]]
    rest = filter (`notElem` "everything" : concat hierarchies) $
           map fst warningGroups

-- | Find the smallest group in every hierarchy which a warning
-- belongs to, excluding Weverything.
smallestGroups :: WarningFlag -> [String]
smallestGroups flag = mapMaybe go warningHierarchies where
    -- Because each hierarchy is arranged from smallest to largest,
    -- the first group we find in a hierarchy which contains the flag
    -- is the smallest.
    go (group:rest) = fromMaybe (go rest) $ do
        flags <- lookup group warningGroups
        guard (flag `elem` flags)
        pure (Just group)
    go [] = Nothing

-- | Warnings enabled unless specified otherwise
standardWarnings :: [WarningFlag]
standardWarnings -- see Note [Documenting warning flags]
    = [ Opt_WarnOverlappingPatterns,
        Opt_WarnWarningsDeprecations,
        Opt_WarnDeprecatedFlags,
        Opt_WarnDeferredTypeErrors,
        Opt_WarnTypedHoles,
        Opt_WarnDeferredOutOfScopeVariables,
        Opt_WarnPartialTypeSignatures,
        Opt_WarnUnrecognisedPragmas,
        Opt_WarnDuplicateExports,
        Opt_WarnOverflowedLiterals,
        Opt_WarnEmptyEnumerations,
        Opt_WarnMissingFields,
        Opt_WarnMissingMethods,
        Opt_WarnWrongDoBind,
        Opt_WarnUnsupportedCallingConventions,
        Opt_WarnDodgyForeignImports,
        Opt_WarnInlineRuleShadowing,
        Opt_WarnAlternativeLayoutRuleTransitional,
        Opt_WarnUnsupportedLlvmVersion,
        Opt_WarnTabs,
        Opt_WarnUnrecognisedWarningFlags,
        Opt_WarnSimplifiableClassConstraints
      ]

-- | Things you get with -W
minusWOpts :: [WarningFlag]
minusWOpts
    = standardWarnings ++
      [ Opt_WarnUnusedTopBinds,
        Opt_WarnUnusedLocalBinds,
        Opt_WarnUnusedPatternBinds,
        Opt_WarnUnusedMatches,
        Opt_WarnUnusedForalls,
        Opt_WarnUnusedImports,
        Opt_WarnIncompletePatterns,
        Opt_WarnDodgyExports,
        Opt_WarnDodgyImports,
        Opt_WarnUnbangedStrictPatterns
      ]

-- | Things you get with -Wall
minusWallOpts :: [WarningFlag]
minusWallOpts
    = minusWOpts ++
      [ Opt_WarnTypeDefaults,
        Opt_WarnNameShadowing,
        Opt_WarnMissingSignatures,
        Opt_WarnHiShadows,
        Opt_WarnOrphans,
        Opt_WarnUnusedDoBind,
        Opt_WarnTrustworthySafe,
        Opt_WarnUntickedPromotedConstructors,
        Opt_WarnMissingPatternSynonymSignatures
      ]

-- | Things you get with -Weverything, i.e. *all* known warnings flags
minusWeverythingOpts :: [WarningFlag]
minusWeverythingOpts = [ toEnum 0 .. ]

-- | Things you get with -Wcompat.
--
-- This is intended to group together warnings that will be enabled by default
-- at some point in the future, so that library authors eager to make their
-- code future compatible to fix issues before they even generate warnings.
minusWcompatOpts :: [WarningFlag]
minusWcompatOpts
    = [ Opt_WarnMissingMonadFailInstances
      , Opt_WarnSemigroup
      , Opt_WarnNonCanonicalMonoidInstances
      ]

enableUnusedBinds :: DynP ()
enableUnusedBinds = mapM_ setWarningFlag unusedBindsFlags

disableUnusedBinds :: DynP ()
disableUnusedBinds = mapM_ unSetWarningFlag unusedBindsFlags

-- Things you get with -Wunused-binds
unusedBindsFlags :: [WarningFlag]
unusedBindsFlags = [ Opt_WarnUnusedTopBinds
                   , Opt_WarnUnusedLocalBinds
                   , Opt_WarnUnusedPatternBinds
                   ]

setWarnSafe :: Bool -> DynP ()
setWarnSafe True  = getCurLoc >>= \l -> upd (\d -> d { warnSafeOnLoc = l })
setWarnSafe False = return ()

setWarnUnsafe :: Bool -> DynP ()
setWarnUnsafe True  = getCurLoc >>= \l -> upd (\d -> d { warnUnsafeOnLoc = l })
setWarnUnsafe False = return ()

setWarningFlag, unSetWarningFlag :: WarningFlag -> DynP ()
setWarningFlag   f = upd (\dfs -> wopt_set dfs f)
unSetWarningFlag f = upd (\dfs -> wopt_unset dfs f)

setFatalWarningFlag, unSetFatalWarningFlag :: WarningFlag -> DynP ()
setFatalWarningFlag   f = upd (\dfs -> wopt_set_fatal dfs f)
unSetFatalWarningFlag f = upd (\dfs -> wopt_unset_fatal dfs f)

warningReasonMsg :: DynFlags -> WarnReason -> Maybe String
warningReasonMsg _dflags NoReason = Nothing
warningReasonMsg dflags (Reason flag) = toName <$> flagSpecOf flag
  where
    toName spec = "-W" ++ flagSpecName spec ++ flagGrp
    flagGrp
      | gopt Opt_ShowWarnGroups dflags =
            case smallestGroups flag of
              [] -> ""
              groups -> " (in " ++ intercalate ", " (map ("-W"++) groups) ++ ")"
      | otherwise = ""
