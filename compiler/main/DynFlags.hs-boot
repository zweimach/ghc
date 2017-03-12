
module DynFlags
    ( module DynFlags.Type
    , module DynFlags
    , DumpFlag
    ) where

import Platform
import {-# SOURCE #-} DynFlags.Type
import {-# SOURCE #-} DynFlags.DumpFlags

targetPlatform       :: DynFlags -> Platform
hasPprDebug          :: DynFlags -> Bool
hasNoDebugOutput     :: DynFlags -> Bool
useUnicodeSyntax     :: DynFlags -> Bool

unsafeGlobalDynFlags :: DynFlags