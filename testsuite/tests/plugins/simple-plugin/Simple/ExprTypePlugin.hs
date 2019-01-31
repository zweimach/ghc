{-# LANGUAGE PatternGuards #-}
module Simple.ExprTypePlugin where

import Control.Monad.IO.Class
import Plugins
import HscTypes
import TcRnTypes
import TcType
import TcHsSyn
import DynFlags (unsafeGlobalDynFlags)
import HsExtension
import HsExpr
import Outputable
import SrcLoc
import Var
import Type
import Data.IORef
import Data.Typeable (Typeable, cast)
import Data.Data (Data, gmapQ)
import Data.List
import Data.Function (on)

plugin :: Plugin
plugin = defaultPlugin { typeCheckResultAction = typecheckPlugin }


typecheckPlugin :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
typecheckPlugin [rng] _ tc
  = do output <- liftIO $ showExpr r $ tcg_binds tc
       liftIO $ putStrLn $ "expr type at " ++ rng ++ ": " ++ output
       return tc
  where r = readRange rng
typecheckPlugin _ _ tc
  = do liftIO (putStrLn
                 "ExprTypePlugin requires one argument in the form of r:c-r:c")
       return tc

type Range = (Int, Int, Int, Int)

readRange :: String -> Range
readRange s = ( read (section (-1) col1 s)
              , read (section col1 dash s)
              , read (section dash col2 s)
              , read (section col2 (length s) s) )
  where [col1,dash,col2] = findIndices (`elem` ":-") s
        section i j = take (j-i-1) . drop (i+1)

locToRange :: SrcSpan -> Range
locToRange (RealSrcSpan rs) = (srcSpanStartLine rs, srcSpanStartCol rs
                              , srcSpanEndLine rs, srcSpanEndCol rs)
locToRange (UnhelpfulSpan _) = (-1, -1, -1, -1)

isInsideRange :: Range -> Range -> Bool
isInsideRange (sr2, sc2, er2, ec2) (sr1, sc1, er1, ec1)
 = (sr1 < sr2 || (sr1 == sr2 && sc1 <= sc2))
     && (er1 > er2 || (er1 == er2 && ec1 >= ec2))

rangeLength :: Range -> (Int, Int)
rangeLength (sr, sc, er, ec) = (er - sr, ec - sc)

showExpr :: (Data a, Typeable a) => Range -> a -> IO String
showExpr r e
 = do let filtered = filter ((`isInsideRange` r) . locToRange . getLoc)
                            (subexpressions e)
          found = maximumBy (compare `on` (rangeLength . locToRange . getLoc))
                    filtered
      if not (null filtered) then showPrimExpr found
                             else return "<no expression found>"

showPrimExpr :: LHsExpr GhcTc -> IO String
showPrimExpr e = showType (hsExprType (unLoc e))

subexpressions :: (Data a, Typeable a) => a -> [LHsExpr GhcTc]
subexpressions x = concat $ gmapQ go x
  where go :: (Data d, Typeable d) => d -> [LHsExpr GhcTc]
        go e = mkQ [] (:[]) e ++ concat (gmapQ go e)

concretizeType :: Type -> IO Type
concretizeType typ | Just tv <- getTyVar_maybe typ
             , isTcTyVar tv
             , MetaTv { mtv_ref = ref } <- tcTyVarDetails tv
  = do details <- readIORef ref
       return $ case details of Indirect t -> t
                                Flexi -> typ
  | Just (fun, arg) <- splitAppTy_maybe typ
  = mkAppTy <$> concretizeType fun <*> concretizeType arg
  | Just (tc, args) <- splitTyConApp_maybe typ
  = mkTyConApp tc <$> mapM concretizeType args
  | (tv, typ') <- splitForAllTyVarBndrs typ
  , not (null tv)
  = mkForAllTys tv <$> concretizeType typ'
  | Just (arg, res) <- splitFunTy_maybe typ
  = mkFunTy <$> concretizeType arg <*> concretizeType res
  | otherwise = return typ

showType :: Type -> IO String
showType typ = showOneLine . ppr <$> concretizeType typ

mkQ :: ( Typeable a, Typeable b ) => r -> (b -> r) -> a -> r
(r `mkQ` br) a = case cast a of
                        Just b  -> br b
                        Nothing -> r

showOneLine :: SDoc -> String
showOneLine = showSDocOneLine unsafeGlobalDynFlags
