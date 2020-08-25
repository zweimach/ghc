{-# LANGUAGE ScopedTypeVariables #-}

-- import Data.List
-- import GHC.Types.SrcLoc
import GHC hiding (moduleName)
import GHC.Driver.Session
import GHC.Hs.Dump
-- import GHC.Hs.Exact hiding (ExactPrint())
import GHC.Utils.Outputable hiding (space)
import System.Environment( getArgs )
import System.Exit
import System.FilePath
import ExactPrint
-- exactPrint = undefined
-- showGhc = undefined

-- ---------------------------------------------------------------------

tt :: IO ()
tt = testOneFile "/home/alanz/mysrc/git.haskell.org/ghc/_build/stage1/lib"
  -- "Test.hs"
 -- "../../testsuite/tests/printer/Ppr001.hs"
 -- "../../testsuite/tests/printer/Ppr002.hs"
 -- "../../testsuite/tests/printer/Ppr003.hs"
 -- "../../testsuite/tests/printer/Ppr004.hs"
 -- "../../testsuite/tests/printer/Ppr005.hs"
 -- "../../testsuite/tests/qualifieddo/should_compile/qdocompile001.hs"
 -- "../../testsuite/tests/printer/Ppr006.hs"
 -- "../../testsuite/tests/printer/Ppr007.hs"
 -- "../../testsuite/tests/printer/Ppr008.hs"
 -- "../../testsuite/tests/hiefile/should_compile/hie008.hs"
 -- "../../testsuite/tests/printer/Ppr009.hs"
 "../../testsuite/tests/printer/Ppr011.hs"
 -- "../../testsuite/tests/printer/Ppr012.hs"

-- exact = ppr

-- ---------------------------------------------------------------------

usage :: String
usage = unlines
    [ "usage: check-ppr (libdir) (file)"
    , ""
    , "where libdir is the GHC library directory (e.g. the output of"
    , "ghc --print-libdir) and file is the file to parse."
    ]

main :: IO()
main = do
  args <- getArgs
  case args of
   [libdir,fileName] -> testOneFile libdir fileName
   _ -> putStrLn usage

testOneFile :: FilePath -> String -> IO ()
testOneFile libdir fileName = do
       p <- parseOneFile libdir fileName
       putStrLn $ "\n\ngot p"
       let
         origAst = showSDoc unsafeGlobalDynFlags
                     $ showAstData BlankSrcSpanFile NoBlankApiAnnotations
                                                         (pm_parsed_source p)
         anns'   = pm_annotations p
         -- pped    = pragmas ++ "\n" ++ (exactPrint $ pm_parsed_source p)
         pped    = exactPrint (pm_parsed_source p) anns'
         -- pragmas = getPragmas anns'

         newFile = dropExtension fileName <.> "ppr" <.> takeExtension fileName
         astFile = fileName <.> "ast"
         newAstFile = fileName <.> "ast.new"

       putStrLn $ "\n\nabout to writeFile"
       writeFile astFile origAst
       putStrLn $ "\n\nabout to pp"
       writeFile newFile pped

       -- putStrLn $ "anns':" ++ showGhc (apiAnnRogueComments anns')

       p' <- parseOneFile libdir newFile

       let newAstStr :: String
           newAstStr = showSDoc unsafeGlobalDynFlags
                         $ showAstData BlankSrcSpanFile NoBlankApiAnnotations
                                                         (pm_parsed_source p')
       writeFile newAstFile newAstStr

       -- putStrLn $ "\n\nanns':" ++ showGhc (apiAnnRogueComments anns')

       if origAst == newAstStr
         then do
           -- putStrLn "ASTs matched"
           exitSuccess
         else do
           putStrLn "AST Match Failed"
           -- putStrLn "\n===================================\nOrig\n\n"
           -- putStrLn origAst
           putStrLn "\n===================================\nNew\n\n"
           putStrLn newAstStr
           exitFailure


parseOneFile :: FilePath -> FilePath -> IO ParsedModule
parseOneFile libdir fileName = do
       let modByFile m =
             case ml_hs_file $ ms_location m of
               Nothing -> False
               Just fn -> fn == fileName
       runGhc (Just libdir) $ do
         dflags <- getSessionDynFlags
         let dflags2 = dflags `gopt_set` Opt_KeepRawTokenStream
         _ <- setSessionDynFlags dflags2
         addTarget Target { targetId = TargetFile fileName Nothing
                          , targetAllowObjCode = True
                          , targetContents = Nothing }
         _ <- load LoadAllTargets
         graph <- getModuleGraph
         let
           modSum = case filter modByFile (mgModSummaries graph) of
                     [x] -> x
                     xs -> error $ "Can't find module, got:"
                              ++ show (map (ml_hs_file . ms_location) xs)
         parseModule modSum

-- getPragmas :: ApiAnns -> String
-- getPragmas anns' = pragmaStr
--   where
--     tokComment (L _ (AnnBlockComment s)) = s
--     tokComment (L _ (AnnLineComment  s)) = s
--     tokComment _ = ""

--     comments' = map tokComment $ sortRealLocated $ apiAnnRogueComments anns'
--     pragmas = filter (\c -> isPrefixOf "{-#" c ) comments'
--     pragmaStr = intercalate "\n" pragmas

-- pp :: (Outputable a) => a -> String
-- pp a = showPpr unsafeGlobalDynFlags a

-- ---------------------------------------------------------------------
