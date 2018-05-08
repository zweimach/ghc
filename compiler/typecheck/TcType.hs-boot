module TcType where
import Binary
import Outputable( SDoc )

data MetaDetails

data TcTyVarDetails
instance Binary TcTyVarDetails

pprTcTyVarDetails :: TcTyVarDetails -> SDoc
vanillaSkolemTv :: TcTyVarDetails
