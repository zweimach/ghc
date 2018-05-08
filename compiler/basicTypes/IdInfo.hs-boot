module IdInfo where
import Binary
import GhcPrelude
import Outputable

data IdInfo
data IdDetails

instance Binary IdInfo
instance Binary IdDetails

vanillaIdInfo :: IdInfo
coVarDetails :: IdDetails
isCoVarDetails :: IdDetails -> Bool
pprIdDetails :: IdDetails -> SDoc

