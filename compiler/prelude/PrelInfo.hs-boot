module PrelInfo where

import Unique
import Name

-- Due to import from IfaceType
lookupKnownKeyName :: Unique -> Maybe Name
