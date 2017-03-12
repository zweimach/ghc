module DynFlags.Parser where

import CmdLineParser

import DynFlags.Type

import Control.Monad

{- **********************************************************************
%*                                                                      *
                DynFlags constructors
%*                                                                      *
%********************************************************************* -}

type DynP = EwM (CmdLineP DynFlags)

upd :: (DynFlags -> DynFlags) -> DynP ()
upd f = liftEwM (do dflags <- getCmdLineState
                    putCmdLineState $! f dflags)

updM :: (DynFlags -> DynP DynFlags) -> DynP ()
updM f = do dflags <- liftEwM getCmdLineState
            dflags' <- f dflags
            liftEwM $ putCmdLineState $! dflags'

--------------- Constructor functions for OptKind -----------------
noArg :: (DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
noArg fn = NoArg (upd fn)

noArgM :: (DynFlags -> DynP DynFlags) -> OptKind (CmdLineP DynFlags)
noArgM fn = NoArg (updM fn)

hasArg :: (String -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
hasArg fn = HasArg (upd . fn)

sepArg :: (String -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
sepArg fn = SepArg (upd . fn)

intSuffix :: (Int -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
intSuffix fn = IntSuffix (\n -> upd (fn n))

intSuffixM :: (Int -> DynFlags -> DynP DynFlags) -> OptKind (CmdLineP DynFlags)
intSuffixM fn = IntSuffix (\n -> updM (fn n))

floatSuffix :: (Float -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
floatSuffix fn = FloatSuffix (\n -> upd (fn n))

optIntSuffixM :: (Maybe Int -> DynFlags -> DynP DynFlags)
              -> OptKind (CmdLineP DynFlags)
optIntSuffixM fn = OptIntSuffix (\mi -> updM (fn mi))


-- | A change in flag state.
type TurnOnFlag = Bool   -- True  <=> we are turning the flag on
                         -- False <=> we are turning the flag off
turnOn  :: TurnOnFlag; turnOn  = True
turnOff :: TurnOnFlag; turnOff = False

nop :: TurnOnFlag -> DynP ()
nop _ = return ()




data FlagSpec flag
   = FlagSpec
       { flagSpecName :: String   -- ^ Flag in string form
       , flagSpecFlag :: flag     -- ^ Flag in internal form
       , flagSpecAction :: (TurnOnFlag -> DynP ())
           -- ^ Extra action to run when the flag is found
           -- Typically, emit a warning or error
       , flagSpecGhcMode :: GhcFlagMode
           -- ^ In which ghc mode the flag has effect
       }

-- | Define a new flag.
flagSpec :: String -> flag -> (Deprecation, FlagSpec flag)
flagSpec name flag = flagSpec' name flag nop

-- | Define a new flag with an effect.
flagSpec' :: String -> flag -> (TurnOnFlag -> DynP ())
          -> (Deprecation, FlagSpec flag)
flagSpec' name flag act = (NotDeprecated, FlagSpec name flag act AllModes)

-- | Define a new deprecated flag with an effect.
depFlagSpecOp :: String -> flag -> (TurnOnFlag -> DynP ()) -> String
            -> (Deprecation, FlagSpec flag)
depFlagSpecOp name flag act dep =
    (Deprecated, snd (flagSpec' name flag (\f -> act f >> deprecate dep)))

-- | Define a new deprecated flag.
depFlagSpec :: String -> flag -> String
            -> (Deprecation, FlagSpec flag)
depFlagSpec name flag dep = depFlagSpecOp name flag nop dep

-- | Define a new deprecated flag with an effect where the deprecation message
-- depends on the flag value
depFlagSpecOp' :: String
             -> flag
             -> (TurnOnFlag -> DynP ())
             -> (TurnOnFlag -> String)
             -> (Deprecation, FlagSpec flag)
depFlagSpecOp' name flag act dep =
    (Deprecated, FlagSpec name flag (\f -> act f >> (deprecate $ dep f))
                                                                       AllModes)

-- | Define a new deprecated flag where the deprecation message
-- depends on the flag value
depFlagSpec' :: String
             -> flag
             -> (TurnOnFlag -> String)
             -> (Deprecation, FlagSpec flag)
depFlagSpec' name flag dep = depFlagSpecOp' name flag nop dep


-- | Define a new deprecated flag where the deprecation message
-- is shown depending on the flag value
depFlagSpecCond :: String
                -> flag
                -> (TurnOnFlag -> Bool)
                -> String
                -> (Deprecation, FlagSpec flag)
depFlagSpecCond name flag cond dep =
    (Deprecated, FlagSpec name flag (\f -> when (cond f) $ deprecate dep)
                                                                       AllModes)

-- | Define a new flag for GHCi.
flagGhciSpec :: String -> flag -> (Deprecation, FlagSpec flag)
flagGhciSpec name flag = flagGhciSpec' name flag nop

-- | Define a new flag for GHCi with an effect.
flagGhciSpec' :: String -> flag -> (TurnOnFlag -> DynP ())
              -> (Deprecation, FlagSpec flag)
flagGhciSpec' name flag act = (NotDeprecated, FlagSpec name flag act OnlyGhci)

-- | Define a new flag invisible to CLI completion.
flagHiddenSpec :: String -> flag -> (Deprecation, FlagSpec flag)
flagHiddenSpec name flag = flagHiddenSpec' name flag nop

-- | Define a new flag invisible to CLI completion with an effect.
flagHiddenSpec' :: String -> flag -> (TurnOnFlag -> DynP ())
                -> (Deprecation, FlagSpec flag)
flagHiddenSpec' name flag act = (NotDeprecated, FlagSpec name flag act
                                                                     HiddenFlag)

-- | Hide a 'FlagSpec' from being displayed in @--show-options@.
--
-- This is for example useful for flags that are obsolete, but should not
-- (yet) be deprecated for compatibility reasons.
hideFlag :: (Deprecation, FlagSpec a) -> (Deprecation, FlagSpec a)
hideFlag (dep, fs) = (dep, fs { flagSpecGhcMode = HiddenFlag })

mkFlag :: TurnOnFlag            -- ^ True <=> it should be turned on
       -> String                -- ^ The flag prefix
       -> (flag -> DynP ())     -- ^ What to do when the flag is found
       -> (Deprecation, FlagSpec flag)  -- ^ Specification of
                                        -- this particular flag
       -> (Deprecation, Flag (CmdLineP DynFlags))
mkFlag turn_on flagPrefix f (dep, (FlagSpec name flag extra_action mode))
    = (dep,
       Flag (flagPrefix ++ name) (NoArg (f flag >> extra_action turn_on)) mode)

----------------Helpers to make flags and keep deprecation information----------

type FlagMaker m = String -> OptKind m -> Flag m
type DynFlagMaker = FlagMaker (CmdLineP DynFlags)
data Deprecation = NotDeprecated | Deprecated deriving (Eq, Ord)

-- Make a non-deprecated flag
make_ord_flag :: DynFlagMaker -> String -> OptKind (CmdLineP DynFlags)
              -> (Deprecation, Flag (CmdLineP DynFlags))
make_ord_flag fm name kind = (NotDeprecated, fm name kind)

-- Make a deprecated flag
make_dep_flag :: DynFlagMaker -> String -> OptKind (CmdLineP DynFlags) -> String
                 -> (Deprecation, Flag (CmdLineP DynFlags))
make_dep_flag fm name kind message = (Deprecated,
                                      fm name $ add_dep_message kind message)

add_dep_message :: OptKind (CmdLineP DynFlags) -> String
                -> OptKind (CmdLineP DynFlags)
add_dep_message (NoArg f) message = NoArg $ f >> deprecate message
add_dep_message (HasArg f) message = HasArg $ \s -> f s >> deprecate message
add_dep_message (SepArg f) message = SepArg $ \s -> f s >> deprecate message
add_dep_message (Prefix f) message = Prefix $ \s -> f s >> deprecate message
add_dep_message (OptPrefix f) message =
                                  OptPrefix $ \s -> f s >> deprecate message
add_dep_message (OptIntSuffix f) message =
                               OptIntSuffix $ \oi -> f oi >> deprecate message
add_dep_message (IntSuffix f) message =
                                  IntSuffix $ \i -> f i >> deprecate message
add_dep_message (FloatSuffix f) message =
                                FloatSuffix $ \fl -> f fl >> deprecate message
add_dep_message (PassFlag f) message =
                                   PassFlag $ \s -> f s >> deprecate message
add_dep_message (AnySuffix f) message =
                                  AnySuffix $ \s -> f s >> deprecate message
add_dep_message (PrefixPred pred f) message =
                            PrefixPred pred $ \s -> f s >> deprecate message
add_dep_message (AnySuffixPred pred f) message =
                         AnySuffixPred pred $ \s -> f s >> deprecate message
