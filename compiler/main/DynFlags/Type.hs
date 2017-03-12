module DynFlags.Type where

import BasicTypes
import Outputable
import Json
import Module
import Platform
import SrcLoc
import qualified EnumSet
import EnumSet (EnumSet)
import PlatformConstants
import PackageConfig
import {-# SOURCE #-} Packages
import {-# SOURCE #-} Hooks

import {-# SOURCE #-} DynFlags.LogOutput
import {-# SOURCE #-} DynFlags.DumpFlags
import {-# SOURCE #-} DynFlags.WarningFlags
import {-# SOURCE #-} DynFlags.GeneralFlags
import {-# SOURCE #-} DynFlags.Ways
import qualified GHC.LanguageExtensions as LangExt

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader
import Data.IORef
import Data.Map (Map)
import Data.Set (Set)
import Data.List (delete)


data OnOff a = On a
             | Off a
  deriving (Eq, Show)

instance Outputable a => Outputable (OnOff a) where
  ppr (On x)  = text "On" <+> ppr x
  ppr (Off x) = text "Off" <+> ppr x

data OverridingBool
  = Auto
  | Always
  | Never
  deriving Show

overrideWith :: Bool -> OverridingBool -> Bool
overrideWith b Auto   = b
overrideWith _ Always = True
overrideWith _ Never  = False

-- | Used when outputting warnings: if a reason is given, it is
-- displayed. If a warning isn't controlled by a flag, this is made
-- explicit at the point of use.
data WarnReason = NoReason | Reason !WarningFlag
  deriving Show

instance Outputable WarnReason where
  ppr = text . show

instance ToJson WarnReason where
  json NoReason = JSNull
  json (Reason wf) = JSString (show wf)


-- -----------------------------------------------------------------------------
-- Compiler modes

-- | The target code type of the compilation (if any).
--
-- Whenever you change the target, also make sure to set 'ghcLink' to
-- something sensible.
--
-- 'HscNothing' can be used to avoid generating any output, however, note
-- that:
--
--  * If a program uses Template Haskell the typechecker may try to run code
--    from an imported module.  This will fail if no code has been generated
--    for this module.  You can use 'GHC.needsTemplateHaskell' to detect
--    whether this might be the case and choose to either switch to a
--    different target or avoid typechecking such modules.  (The latter may be
--    preferable for security reasons.)
--
data HscTarget
  = HscC           -- ^ Generate C code.
  | HscAsm         -- ^ Generate assembly using the native code generator.
  | HscLlvm        -- ^ Generate assembly using the llvm code generator.
  | HscInterpreted -- ^ Generate bytecode.  (Requires 'LinkInMemory')
  | HscNothing     -- ^ Don't generate any code.  See notes above.
  deriving (Eq, Show)

-- | Will this target result in an object file on the disk?
isObjectTarget :: HscTarget -> Bool
isObjectTarget HscC     = True
isObjectTarget HscAsm   = True
isObjectTarget HscLlvm  = True
isObjectTarget _        = False

-- | Does this target retain *all* top-level bindings for a module,
-- rather than just the exported bindings, in the TypeEnv and compiled
-- code (if any)?  In interpreted mode we do this, so that GHCi can
-- call functions inside a module.  In HscNothing mode we also do it,
-- so that Haddock can get access to the GlobalRdrEnv for a module
-- after typechecking it.
targetRetainsAllBindings :: HscTarget -> Bool
targetRetainsAllBindings HscInterpreted = True
targetRetainsAllBindings HscNothing     = True
targetRetainsAllBindings _              = False

-- | The 'GhcMode' tells us whether we're doing multi-module
-- compilation (controlled via the "GHC" API) or one-shot
-- (single-module) compilation.  This makes a difference primarily to
-- the "Finder": in one-shot mode we look for interface files for
-- imported modules, but in multi-module mode we look for source files
-- in order to check whether they need to be recompiled.
data GhcMode
  = CompManager         -- ^ @\-\-make@, GHCi, etc.
  | OneShot             -- ^ @ghc -c Foo.hs@
  | MkDepend            -- ^ @ghc -M@, see "Finder" for why we need this
  deriving Eq

instance Outputable GhcMode where
  ppr CompManager = text "CompManager"
  ppr OneShot     = text "OneShot"
  ppr MkDepend    = text "MkDepend"

isOneShot :: GhcMode -> Bool
isOneShot OneShot = True
isOneShot _other  = False

-- | What to do in the link step, if there is one.
data GhcLink
  = NoLink              -- ^ Don't link at all
  | LinkBinary          -- ^ Link object code into a binary
  | LinkInMemory        -- ^ Use the in-memory dynamic linker (works for both
                        --   bytecode and object code).
  | LinkDynLib          -- ^ Link objects into a dynamic lib (DLL on Windows, DSO on ELF platforms)
  | LinkStaticLib       -- ^ Link objects into a static lib
  deriving (Eq, Show)

isNoLink :: GhcLink -> Bool
isNoLink NoLink = True
isNoLink _      = False

data DynLibLoader
  = Deployable
  | SystemDependent
  deriving Eq

data RtsOptsEnabled = RtsOptsNone | RtsOptsSafeOnly | RtsOptsAll
  deriving (Show)


-- -----------------------------------------------------------------------------
-- Linker/compiler information

-- LinkerInfo contains any extra options needed by the system linker.
data LinkerInfo
  = GnuLD    [Option]
  | GnuGold  [Option]
  | DarwinLD [Option]
  | SolarisLD [Option]
  | AixLD    [Option]
  | UnknownLD
  deriving Eq

-- CompilerInfo tells us which C compiler we're using
data CompilerInfo
   = GCC
   | Clang
   | AppleClang
   | AppleClang51
   | UnknownCC
   deriving Eq


-- -----------------------------------------------------------------------------
-- SSE and AVX

-- TODO: Instead of using a separate predicate (i.e. isSse2Enabled) to
-- check if SSE is enabled, we might have x86-64 imply the -msse2
-- flag.

data SseVersion = SSE1
                | SSE2
                | SSE3
                | SSE4
                | SSE42
                deriving (Eq, Ord)


-- -----------------------------------------------------------------------------
-- Command-line options

-- | When invoking external tools as part of the compilation pipeline, we
-- pass these a sequence of options on the command-line. Rather than
-- just using a list of Strings, we use a type that allows us to distinguish
-- between filepaths and 'other stuff'. The reason for this is that
-- this type gives us a handle on transforming filenames, and filenames only,
-- to whatever format they're expected to be on a particular platform.
data Option
 = FileOption -- an entry that _contains_ filename(s) / filepaths.
              String  -- a non-filepath prefix that shouldn't be
                      -- transformed (e.g., "/out=")
              String  -- the filepath/filename portion
 | Option     String
 deriving ( Eq )

showOpt :: Option -> String
showOpt (FileOption pre f) = pre ++ f
showOpt (Option s)  = s


-- -----------------------------------------------------------------------------
-- Language variants

data Language = Haskell98 | Haskell2010
   deriving (Eq, Enum, Show)

instance Outputable Language where
    ppr = text . show

-- | The various Safe Haskell modes
data SafeHaskellMode
   = Sf_None
   | Sf_Unsafe
   | Sf_Trustworthy
   | Sf_Safe
   deriving (Eq)

instance Show SafeHaskellMode where
    show Sf_None         = "None"
    show Sf_Unsafe       = "Unsafe"
    show Sf_Trustworthy  = "Trustworthy"
    show Sf_Safe         = "Safe"

instance Outputable SafeHaskellMode where
    ppr = text . show


-- -----------------------------------------------------------------------------
-- The package system

-- | We accept flags which make packages visible, but how they select
-- the package varies; this data type reflects what selection criterion
-- is used.
data PackageArg =
      PackageArg String    -- ^ @-package@, by 'PackageName'
    | UnitIdArg UnitId     -- ^ @-package-id@, by 'UnitId'
  deriving (Eq, Show)

instance Outputable PackageArg where
    ppr (PackageArg pn) = text "package" <+> text pn
    ppr (UnitIdArg uid) = text "unit" <+> ppr uid

-- | Represents the renaming that may be associated with an exposed
-- package, e.g. the @rns@ part of @-package "foo (rns)"@.
--
-- Here are some example parsings of the package flags (where
-- a string literal is punned to be a 'ModuleName':
--
--      * @-package foo@ is @ModRenaming True []@
--      * @-package foo ()@ is @ModRenaming False []@
--      * @-package foo (A)@ is @ModRenaming False [("A", "A")]@
--      * @-package foo (A as B)@ is @ModRenaming False [("A", "B")]@
--      * @-package foo with (A as B)@ is @ModRenaming True [("A", "B")]@
data ModRenaming = ModRenaming {
    modRenamingWithImplicit :: Bool, -- ^ Bring all exposed modules into scope?
    modRenamings :: [(ModuleName, ModuleName)] -- ^ Bring module @m@ into scope
                                               --   under name @n@.
  } deriving (Eq)

instance Outputable ModRenaming where
    ppr (ModRenaming b rns) = ppr b <+> parens (ppr rns)

-- | Flags for manipulating the set of non-broken packages.
newtype IgnorePackageFlag = IgnorePackage String -- ^ @-ignore-package@
  deriving (Eq)

-- | Flags for manipulating package trust.
data TrustFlag
  = TrustPackage    String -- ^ @-trust@
  | DistrustPackage String -- ^ @-distrust@
  deriving (Eq)

-- | Flags for manipulating packages visibility.
data PackageFlag
  = ExposePackage   String PackageArg ModRenaming -- ^ @-package@, @-package-id@
  | HidePackage     String -- ^ @-hide-package@
  deriving (Eq)
-- NB: equality instance is used by InteractiveUI to test if
-- package flags have changed.

instance Outputable PackageFlag where
    ppr (ExposePackage n arg rn) = text n <> braces (ppr arg <+> ppr rn)
    ppr (HidePackage str) = text "-hide-package" <+> text str

data PkgConfRef
  = GlobalPkgConf
  | UserPkgConf
  | PkgConfFile FilePath


-- -----------------------------------------------------------------------------
-- The DynFlags type

-- | Contains not only a collection of 'GeneralFlag's but also a plethora of
-- information relating to the compilation of a single file or GHC session
data DynFlags = DynFlags {
  ghcMode               :: GhcMode,
  ghcLink               :: GhcLink,
  hscTarget             :: HscTarget,
  settings              :: Settings,
  verbosity             :: Int,         -- ^ Verbosity level: see Note [Verbosity levels]
  optLevel              :: Int,         -- ^ Optimisation level
  debugLevel            :: Int,         -- ^ How much debug information to produce
  simplPhases           :: Int,         -- ^ Number of simplifier phases
  maxSimplIterations    :: Int,         -- ^ Max simplifier iterations
  maxPmCheckIterations  :: Int,         -- ^ Max no iterations for pm checking
  ruleCheck             :: Maybe String,
  strictnessBefore      :: [Int],       -- ^ Additional demand analysis

  parMakeCount          :: Maybe Int,   -- ^ The number of modules to compile in parallel
                                        --   in --make mode, where Nothing ==> compile as
                                        --   many in parallel as there are CPUs.

  enableTimeStats       :: Bool,        -- ^ Enable RTS timing statistics?
  ghcHeapSize           :: Maybe Int,   -- ^ The heap size to set.

  maxRelevantBinds      :: Maybe Int,   -- ^ Maximum number of bindings from the type envt
                                        --   to show in type error messages
  maxUncoveredPatterns  :: Int,         -- ^ Maximum number of unmatched patterns to show
                                        --   in non-exhaustiveness warnings
  simplTickFactor       :: Int,         -- ^ Multiplier for simplifier ticks
  specConstrThreshold   :: Maybe Int,   -- ^ Threshold for SpecConstr
  specConstrCount       :: Maybe Int,   -- ^ Max number of specialisations for any one function
  specConstrRecursive   :: Int,         -- ^ Max number of specialisations for recursive types
                                        --   Not optional; otherwise ForceSpecConstr can diverge.
  liberateCaseThreshold :: Maybe Int,   -- ^ Threshold for LiberateCase
  floatLamArgs          :: Maybe Int,   -- ^ Arg count for lambda floating
                                        --   See CoreMonad.FloatOutSwitches

  historySize           :: Int,         -- ^ Simplification history size

  importPaths           :: [FilePath],
  mainModIs             :: Module,
  mainFunIs             :: Maybe String,
  reductionDepth        :: IntWithInf,   -- ^ Typechecker maximum stack depth
  solverIterations      :: IntWithInf,   -- ^ Number of iterations in the constraints solver
                                         --   Typically only 1 is needed

  thisInstalledUnitId   :: InstalledUnitId,
  thisComponentId_      :: Maybe ComponentId,
  thisUnitIdInsts_      :: Maybe [(ModuleName, Module)],

  -- ways
  ways                  :: [Way],       -- ^ Way flags from the command line
  buildTag              :: String,      -- ^ The global \"way\" (e.g. \"p\" for prof)
  rtsBuildTag           :: String,      -- ^ The RTS \"way\"

  -- For object splitting
  splitInfo             :: Maybe (String,Int),

  -- paths etc.
  objectDir             :: Maybe String,
  dylibInstallName      :: Maybe String,
  hiDir                 :: Maybe String,
  stubDir               :: Maybe String,
  dumpDir               :: Maybe String,

  objectSuf             :: String,
  hcSuf                 :: String,
  hiSuf                 :: String,

  canGenerateDynamicToo :: IORef Bool,
  dynObjectSuf          :: String,
  dynHiSuf              :: String,

  -- Packages.isDllName needs to know whether a call is within a
  -- single DLL or not. Normally it does this by seeing if the call
  -- is to the same package, but for the ghc package, we split the
  -- package between 2 DLLs. The dllSplit tells us which sets of
  -- modules are in which package.
  dllSplitFile          :: Maybe FilePath,
  dllSplit              :: Maybe [Set String],

  outputFile            :: Maybe String,
  dynOutputFile         :: Maybe String,
  outputHi              :: Maybe String,
  dynLibLoader          :: DynLibLoader,

  -- | This is set by 'DriverPipeline.runPipeline' based on where
  --    its output is going.
  dumpPrefix            :: Maybe FilePath,

  -- | Override the 'dumpPrefix' set by 'DriverPipeline.runPipeline'.
  --    Set by @-ddump-file-prefix@
  dumpPrefixForce       :: Maybe FilePath,

  ldInputs              :: [Option],

  includePaths          :: [String],
  libraryPaths          :: [String],
  frameworkPaths        :: [String],    -- used on darwin only
  cmdlineFrameworks     :: [String],    -- ditto

  rtsOpts               :: Maybe String,
  rtsOptsEnabled        :: RtsOptsEnabled,
  rtsOptsSuggestions    :: Bool,

  hpcDir                :: String,      -- ^ Path to store the .mix files

  -- Plugins
  pluginModNames        :: [ModuleName],
  pluginModNameOpts     :: [(ModuleName,String)],
  frontendPluginOpts    :: [String],

  -- GHC API hooks
  hooks                 :: Hooks,

  --  For ghc -M
  depMakefile           :: FilePath,
  depIncludePkgDeps     :: Bool,
  depExcludeMods        :: [ModuleName],
  depSuffixes           :: [String],

  --  Package flags
  extraPkgConfs         :: [PkgConfRef] -> [PkgConfRef],
        -- ^ The @-package-db@ flags given on the command line, in the order
        -- they appeared.

  ignorePackageFlags    :: [IgnorePackageFlag],
        -- ^ The @-ignore-package@ flags from the command line
  packageFlags          :: [PackageFlag],
        -- ^ The @-package@ and @-hide-package@ flags from the command-line
  pluginPackageFlags    :: [PackageFlag],
        -- ^ The @-plugin-package-id@ flags from command line
  trustFlags            :: [TrustFlag],
        -- ^ The @-trust@ and @-distrust@ flags
  packageEnv            :: Maybe FilePath,
        -- ^ Filepath to the package environment file (if overriding default)

  -- Package state
  -- NB. do not modify this field, it is calculated by
  -- Packages.initPackages
  pkgDatabase           :: Maybe [(FilePath, [PackageConfig])],
  pkgState              :: PackageState,

  -- Temporary files
  -- These have to be IORefs, because the defaultCleanupHandler needs to
  -- know what to clean when an exception happens
  filesToClean          :: IORef [FilePath],
  dirsToClean           :: IORef (Map FilePath FilePath),
  filesToNotIntermediateClean :: IORef [FilePath],
  -- The next available suffix to uniquely name a temp file, updated atomically
  nextTempSuffix        :: IORef Int,

  -- Names of files which were generated from -ddump-to-file; used to
  -- track which ones we need to truncate because it's our first run
  -- through
  generatedDumps        :: IORef (Set FilePath),

  -- hsc dynamic flags
  dumpFlags             :: EnumSet DumpFlag,
  generalFlags          :: EnumSet GeneralFlag,
  warningFlags          :: EnumSet WarningFlag,
  fatalWarningFlags     :: EnumSet WarningFlag,
  -- Don't change this without updating extensionFlags:
  language              :: Maybe Language,
  -- | Safe Haskell mode
  safeHaskell           :: SafeHaskellMode,
  safeInfer             :: Bool,
  safeInferred          :: Bool,
  -- We store the location of where some extension and flags were turned on so
  -- we can produce accurate error messages when Safe Haskell fails due to
  -- them.
  thOnLoc               :: SrcSpan,
  newDerivOnLoc         :: SrcSpan,
  overlapInstLoc        :: SrcSpan,
  incoherentOnLoc       :: SrcSpan,
  pkgTrustOnLoc         :: SrcSpan,
  warnSafeOnLoc         :: SrcSpan,
  warnUnsafeOnLoc       :: SrcSpan,
  trustworthyOnLoc      :: SrcSpan,
  -- Don't change this without updating extensionFlags:
  extensions            :: [OnOff LangExt.Extension],
  -- extensionFlags should always be equal to
  --     flattenExtensionFlags language extensions
  -- LangExt.Extension is defined in libraries/ghc-boot so that it can be used
  -- by template-haskell
  extensionFlags        :: EnumSet LangExt.Extension,

  -- Unfolding control
  -- See Note [Discounts and thresholds] in CoreUnfold
  ufCreationThreshold   :: Int,
  ufUseThreshold        :: Int,
  ufFunAppDiscount      :: Int,
  ufDictDiscount        :: Int,
  ufKeenessFactor       :: Float,
  ufDearOp              :: Int,
  ufVeryAggressive      :: Bool,

  maxWorkerArgs         :: Int,

  ghciHistSize          :: Int,

  -- | MsgDoc output action: use "ErrUtils" instead of this if you can
  initLogAction         :: IO (Maybe LogOutput),
  log_action            :: LogAction,
  log_finaliser         :: LogFinaliser,
  flushOut              :: FlushOut,
  flushErr              :: FlushErr,

  haddockOptions        :: Maybe String,

  -- | GHCi scripts specified by -ghci-script, in reverse order
  ghciScripts           :: [String],

  -- Output style options
  pprUserLength         :: Int,
  pprCols               :: Int,

  useUnicode            :: Bool,
  useColor              :: OverridingBool,
  canUseColor           :: Bool,

  -- | what kind of {-# SCC #-} to add automatically
  profAuto              :: ProfAuto,

  interactivePrint      :: Maybe String,

  nextWrapperNum        :: IORef (ModuleEnv Int),

  -- | Machine dependent flags (-m<blah> stuff)
  sseVersion            :: Maybe SseVersion,
  avx                   :: Bool,
  avx2                  :: Bool,
  avx512cd              :: Bool, -- Enable AVX-512 Conflict Detection Instructions.
  avx512er              :: Bool, -- Enable AVX-512 Exponential and Reciprocal Instructions.
  avx512f               :: Bool, -- Enable AVX-512 instructions.
  avx512pf              :: Bool, -- Enable AVX-512 PreFetch Instructions.

  -- | Run-time linker information (what options we need, etc.)
  rtldInfo              :: IORef (Maybe LinkerInfo),

  -- | Run-time compiler information
  rtccInfo              :: IORef (Maybe CompilerInfo),

  -- Constants used to control the amount of optimization done.

  -- | Max size, in bytes, of inline array allocations.
  maxInlineAllocSize    :: Int,

  -- | Only inline memcpy if it generates no more than this many
  -- pseudo (roughly: Cmm) instructions.
  maxInlineMemcpyInsns  :: Int,

  -- | Only inline memset if it generates no more than this many
  -- pseudo (roughly: Cmm) instructions.
  maxInlineMemsetInsns  :: Int,

  -- | Reverse the order of error messages in GHC/GHCi
  reverseErrors :: Bool,

  -- | Limit the maximum number of errors to show
  maxErrors             :: Maybe Int,

  -- | Unique supply configuration for testing build determinism
  initialUnique         :: Int,
  uniqueIncrement       :: Int
}

class HasDynFlags m where
    getDynFlags :: m DynFlags

{- It would be desirable to have the more generalised

  instance (MonadTrans t, Monad m, HasDynFlags m) => HasDynFlags (t m) where
      getDynFlags = lift getDynFlags

instance definition. However, that definition would overlap with the
`HasDynFlags (GhcT m)` instance. Instead we define instances for a
couple of common Monad transformers explicitly. -}

instance (Monoid a, Monad m, HasDynFlags m) => HasDynFlags (WriterT a m) where
    getDynFlags = lift getDynFlags

instance (Monad m, HasDynFlags m) => HasDynFlags (ReaderT a m) where
    getDynFlags = lift getDynFlags

instance (Monad m, HasDynFlags m) => HasDynFlags (MaybeT m) where
    getDynFlags = lift getDynFlags

instance (Monad m, HasDynFlags m) => HasDynFlags (ExceptT e m) where
    getDynFlags = lift getDynFlags

class ContainsDynFlags t where
    extractDynFlags :: t -> DynFlags

data ProfAuto
  = NoProfAuto         -- ^ no SCC annotations added
  | ProfAutoAll        -- ^ top-level and nested functions are annotated
  | ProfAutoTop        -- ^ top-level functions annotated only
  | ProfAutoExports    -- ^ exported functions annotated only
  | ProfAutoCalls      -- ^ annotate call-sites
  deriving (Eq,Enum)

data Settings = Settings {
  sTargetPlatform        :: Platform,    -- Filled in by SysTools
  sGhcUsagePath          :: FilePath,    -- Filled in by SysTools
  sGhciUsagePath         :: FilePath,    -- ditto
  sTopDir                :: FilePath,
  sTmpDir                :: String,      -- no trailing '/'
  sProgramName           :: String,
  sProjectVersion        :: String,
  -- You shouldn't need to look things up in rawSettings directly.
  -- They should have their own fields instead.
  sRawSettings           :: [(String, String)],
  sExtraGccViaCFlags     :: [String],
  sSystemPackageConfig   :: FilePath,
  sLdSupportsCompactUnwind :: Bool,
  sLdSupportsBuildId       :: Bool,
  sLdSupportsFilelist      :: Bool,
  sLdIsGnuLd               :: Bool,
  sGccSupportsNoPie        :: Bool,
  -- commands for particular phases
  sPgm_L                 :: String,
  sPgm_P                 :: (String,[Option]),
  sPgm_F                 :: String,
  sPgm_c                 :: (String,[Option]),
  sPgm_s                 :: (String,[Option]),
  sPgm_a                 :: (String,[Option]),
  sPgm_l                 :: (String,[Option]),
  sPgm_dll               :: (String,[Option]),
  sPgm_T                 :: String,
  sPgm_windres           :: String,
  sPgm_libtool           :: String,
  sPgm_lo                :: (String,[Option]), -- LLVM: opt llvm optimiser
  sPgm_lc                :: (String,[Option]), -- LLVM: llc static compiler
  sPgm_i                 :: String,
  -- options for particular phases
  sOpt_L                 :: [String],
  sOpt_P                 :: [String],
  sOpt_F                 :: [String],
  sOpt_c                 :: [String],
  sOpt_a                 :: [String],
  sOpt_l                 :: [String],
  sOpt_windres           :: [String],
  sOpt_lo                :: [String], -- LLVM: llvm optimiser
  sOpt_lc                :: [String], -- LLVM: llc static compiler
  sOpt_i                 :: [String], -- iserv options

  sPlatformConstants     :: PlatformConstants
 }


-- -----------------------------------------------------------------------------
-- Accessors

-- | Set a 'DumpFlag'
dopt_set :: DynFlags -> DumpFlag -> DynFlags
dopt_set dfs f = dfs{ dumpFlags = EnumSet.insert f (dumpFlags dfs) }

-- | Unset a 'DumpFlag'
dopt_unset :: DynFlags -> DumpFlag -> DynFlags
dopt_unset dfs f = dfs{ dumpFlags = EnumSet.delete f (dumpFlags dfs) }

-- | Test whether a 'GeneralFlag' is set
gopt :: GeneralFlag -> DynFlags -> Bool
gopt f dflags  = f `EnumSet.member` generalFlags dflags

-- | Set a 'GeneralFlag'
gopt_set :: DynFlags -> GeneralFlag -> DynFlags
gopt_set dfs f = dfs{ generalFlags = EnumSet.insert f (generalFlags dfs) }

-- | Unset a 'GeneralFlag'
gopt_unset :: DynFlags -> GeneralFlag -> DynFlags
gopt_unset dfs f = dfs{ generalFlags = EnumSet.delete f (generalFlags dfs) }

-- | Test whether a 'WarningFlag' is set
wopt :: WarningFlag -> DynFlags -> Bool
wopt f dflags  = f `EnumSet.member` warningFlags dflags

-- | Set a 'WarningFlag'
wopt_set :: DynFlags -> WarningFlag -> DynFlags
wopt_set dfs f = dfs{ warningFlags = EnumSet.insert f (warningFlags dfs) }

-- | Unset a 'WarningFlag'
wopt_unset :: DynFlags -> WarningFlag -> DynFlags
wopt_unset dfs f = dfs{ warningFlags = EnumSet.delete f (warningFlags dfs) }

-- | Test whether a 'WarningFlag' is set as fatal
wopt_fatal :: WarningFlag -> DynFlags -> Bool
wopt_fatal f dflags = f `EnumSet.member` fatalWarningFlags dflags

-- | Mark a 'WarningFlag' as fatal (do not set the flag)
wopt_set_fatal :: DynFlags -> WarningFlag -> DynFlags
wopt_set_fatal dfs f
    = dfs { fatalWarningFlags = EnumSet.insert f (fatalWarningFlags dfs) }

-- | Mark a 'WarningFlag' as not fatal
wopt_unset_fatal :: DynFlags -> WarningFlag -> DynFlags
wopt_unset_fatal dfs f
    = dfs { fatalWarningFlags = EnumSet.delete f (fatalWarningFlags dfs) }

-- | Test whether a 'LangExt.Extension' is set
xopt :: LangExt.Extension -> DynFlags -> Bool
xopt f dflags = f `EnumSet.member` extensionFlags dflags

-- | Set a 'LangExt.Extension'
xopt_set :: DynFlags -> LangExt.Extension -> DynFlags
xopt_set dfs f
    = let onoffs = On f : extensions dfs
      in dfs { extensions = onoffs,
               extensionFlags = flattenExtensionFlags (language dfs) onoffs }

-- | Unset a 'LangExt.Extension'
xopt_unset :: DynFlags -> LangExt.Extension -> DynFlags
xopt_unset dfs f
    = let onoffs = Off f : extensions dfs
      in dfs { extensions = onoffs,
               extensionFlags = flattenExtensionFlags (language dfs) onoffs }

lang_set :: DynFlags -> Maybe Language -> DynFlags
lang_set dflags lang =
   dflags {
            language = lang,
            extensionFlags = flattenExtensionFlags lang (extensions dflags)
          }

-- -----------------------------------------------------------------------------
-- Language extensions

-- OnOffs accumulate in reverse order, so we use foldr in order to
-- process them in the right order
flattenExtensionFlags :: Maybe Language -> [OnOff LangExt.Extension] -> EnumSet LangExt.Extension
flattenExtensionFlags ml = foldr f defaultExtensionFlags
    where f (On f)  flags = EnumSet.insert f flags
          f (Off f) flags = EnumSet.delete f flags
          defaultExtensionFlags = EnumSet.fromList (languageExtensions ml)

languageExtensions :: Maybe Language -> [LangExt.Extension]

languageExtensions Nothing
    -- Nothing => the default case
    = LangExt.NondecreasingIndentation -- This has been on by default for some time
    : delete LangExt.DatatypeContexts  -- The Haskell' committee decided to
                                       -- remove datatype contexts from the
                                       -- language:
   -- http://www.haskell.org/pipermail/haskell-prime/2011-January/003335.html
      (languageExtensions (Just Haskell2010))

   -- NB: MonoPatBinds is no longer the default

languageExtensions (Just Haskell98)
    = [LangExt.ImplicitPrelude,
       LangExt.MonomorphismRestriction,
       LangExt.NPlusKPatterns,
       LangExt.DatatypeContexts,
       LangExt.TraditionalRecordSyntax,
       LangExt.NondecreasingIndentation
           -- strictly speaking non-standard, but we always had this
           -- on implicitly before the option was added in 7.1, and
           -- turning it off breaks code, so we're keeping it on for
           -- backwards compatibility.  Cabal uses -XHaskell98 by
           -- default unless you specify another language.
      ]

languageExtensions (Just Haskell2010)
    = [LangExt.ImplicitPrelude,
       LangExt.MonomorphismRestriction,
       LangExt.DatatypeContexts,
       LangExt.TraditionalRecordSyntax,
       LangExt.EmptyDataDecls,
       LangExt.ForeignFunctionInterface,
       LangExt.PatternGuards,
       LangExt.DoAndIfThenElse,
       LangExt.RelaxedPolyRec]
