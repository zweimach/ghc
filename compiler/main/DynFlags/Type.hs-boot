module DynFlags.Type where

data DynFlags
data WarnReason
data OverridingBool

pprUserLength        :: DynFlags -> Int
pprCols              :: DynFlags -> Int
useUnicode           :: DynFlags -> Bool
useColor             :: DynFlags -> OverridingBool
canUseColor          :: DynFlags -> Bool
overrideWith         :: Bool -> OverridingBool -> Bool