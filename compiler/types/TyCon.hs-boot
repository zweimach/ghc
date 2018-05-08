module TyCon where

import Binary
import GhcPrelude

data TyCon
instance Binary TyCon

isTupleTyCon        :: TyCon -> Bool
isUnboxedTupleTyCon :: TyCon -> Bool
isFunTyCon          :: TyCon -> Bool
