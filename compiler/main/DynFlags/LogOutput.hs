module DynFlags.LogOutput where

import qualified Pretty
import Outputable
import Json
import {-# SOURCE #-} ErrUtils
import SrcLoc
import DynFlags.Type
import DynFlags.GeneralFlags
import DynFlags.DumpFlags
import DynFlags.WarningFlags

import Data.IORef
import System.IO

--------------------------------------------------------------------------
--
-- Note [JSON Error Messages]
--
-- When the user requests the compiler output to be dumped as json
-- we modify the log_action to collect all the messages in an IORef
-- and then finally in GHC.withCleanupSession the log_finaliser is
-- called which prints out the messages together.
--
-- Before the compiler calls log_action, it has already turned the `ErrMsg`
-- into a formatted message. This means that we lose some possible
-- information to provide to the user but refactoring log_action is quite
-- invasive as it is called in many places. So, for now I left it alone
-- and we can refine its behaviour as users request different output.

type FatalMessager = String -> IO ()

data LogOutput = LogOutput
               { getLogAction :: LogAction
               , getLogFinaliser :: LogFinaliser
               }

defaultLogOutput :: IO (Maybe LogOutput)
defaultLogOutput = return $ Nothing

newtype LogAction
    = LogAction { runLogAction :: DynFlags
                               -> WarnReason
                               -> Severity
                               -> SrcSpan
                               -> PprStyle
                               -> MsgDoc
                               -> IO () }

noopLogAction :: LogAction
noopLogAction = LogAction $ \_ _ _ _ _ _ -> return ()

newtype LogFinaliser = LogFinaliser { runLogFinaliser :: DynFlags -> IO () }

nopLogFinaliser :: LogFinaliser
nopLogFinaliser = LogFinaliser $ const $ return ()

defaultFatalMessager :: FatalMessager
defaultFatalMessager = hPutStrLn stderr

-- See Note [JSON Error Messages]
jsonLogOutput :: IO (Maybe LogOutput)
jsonLogOutput = do
  ref <- newIORef []
  return . Just $ LogOutput (jsonLogAction ref) (jsonLogFinaliser ref)

jsonLogAction :: IORef [SDoc] -> LogAction
jsonLogAction iref
  = LogAction $ \dflags reason severity srcSpan style msg -> do
      addMessage . withPprStyle (mkCodeStyle CStyle) . renderJSON $
        JSObject [ ( "span", json srcSpan )
                 , ( "doc" , JSString (showSDoc dflags msg) )
                 , ( "severity", json severity )
                 , ( "reason" ,   json reason )
                ]
      runLogAction defaultLogAction dflags reason severity srcSpan style msg
  where
    addMessage m = modifyIORef iref (m:)


jsonLogFinaliser :: IORef [SDoc] -> LogFinaliser
jsonLogFinaliser iref = LogFinaliser run
  where
    run dflags = do
      msgs <- readIORef iref
      let fmt_msgs = brackets $ pprWithCommas (blankLine $$) msgs
      output fmt_msgs
      where
        -- dumpSDoc uses log_action to output the dump
        dflags' = dflags { log_action = defaultLogAction }
        output doc = dumpSDoc dflags' neverQualify Opt_D_dump_json "" doc


defaultLogAction :: LogAction
defaultLogAction
    = LogAction action
  where
    action dflags reason severity srcSpan style msg =
      case severity of
      SevOutput      -> printOut msg style
      SevDump        -> printOut (msg $$ blankLine) style
      SevInteractive -> putStrSDoc msg style
      SevInfo        -> printErrs msg style
      SevFatal       -> printErrs msg style
      _              -> do -- otherwise (i.e. SevError or SevWarning)
                           hPutChar stderr '\n'
                           caretDiagnostic <-
                               if gopt Opt_DiagnosticsShowCaret dflags
                               then getCaretDiagnostic severity srcSpan
                               else pure empty
                           printErrs (message $+$ caretDiagnostic)
                               (setStyleColoured True style)
                           -- careful (#2302): printErrs prints in UTF-8,
                           -- whereas converting to string first and using
                           -- hPutStr would just emit the low 8 bits of
                           -- each unicode char.
      where printOut   = defaultLogActionHPrintDoc  dflags stdout
            printErrs  = defaultLogActionHPrintDoc  dflags stderr
            putStrSDoc = defaultLogActionHPutStrDoc dflags stdout
            -- Pretty print the warning flag, if any (#10752)
            message = mkLocMessageAnn flagMsg severity srcSpan msg
            flagMsg = warningReasonMsg dflags reason

-- | Like 'defaultLogActionHPutStrDoc' but appends an extra newline.
defaultLogActionHPrintDoc :: DynFlags -> Handle -> SDoc -> PprStyle -> IO ()
defaultLogActionHPrintDoc dflags h d sty
 = defaultLogActionHPutStrDoc dflags h (d $$ text "") sty

defaultLogActionHPutStrDoc :: DynFlags -> Handle -> SDoc -> PprStyle -> IO ()
defaultLogActionHPutStrDoc dflags h d sty
  -- Don't add a newline at the end, so that successive
  -- calls to this log-action can output all on the same line
  = printSDoc Pretty.PageMode dflags h sty d

newtype FlushOut = FlushOut (IO ())

defaultFlushOut :: FlushOut
defaultFlushOut = FlushOut $ hFlush stdout

newtype FlushErr = FlushErr (IO ())

defaultFlushErr :: FlushErr
defaultFlushErr = FlushErr $ hFlush stderr
