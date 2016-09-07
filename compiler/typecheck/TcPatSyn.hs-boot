module TcPatSyn where

import Name      ( Name )
import Id        ( Id )
import HsSyn     ( PatSynBind, LHsBinds )
import TcRnTypes ( TcM, TcPatSynInfo )
import TcRnMonad ( TcGblEnv)
import TcSigs    ( TcPragEnv )
import Outputable ( Outputable )

tcInferPatSynDecl :: TcPragEnv
                  -> PatSynBind Name Name
                  -> TcM (LHsBinds Id, TcGblEnv)

tcCheckPatSynDecl :: TcPragEnv
                  -> PatSynBind Name Name
                  -> TcPatSynInfo
                  -> TcM (LHsBinds Id, TcGblEnv)

tcPatSynBuilderBind :: PatSynBind Name Name -> TcM (LHsBinds Id)

nonBidirectionalErr :: Outputable name => name -> TcM a
