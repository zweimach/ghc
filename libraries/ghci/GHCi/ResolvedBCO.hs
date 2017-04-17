{-# LANGUAGE RecordWildCards, DeriveGeneric, GeneralizedNewtypeDeriving,
    BangPatterns, MagicHash, UnboxedTuples #-}
module GHCi.ResolvedBCO
  ( ResolvedBCO(..)
  , ResolvedBCOPtr(..)
  ) where

import SizedSeq
import GHCi.RemoteTypes
import GHCi.BreakArray

import Data.Array.Unboxed
import Data.Binary
import GHC.Generics
import GHCi.BinaryArray

-- -----------------------------------------------------------------------------
-- ResolvedBCO

-- A A ResolvedBCO is one in which all the Name references have been
-- resolved to actual addresses or RemoteHValues.
--
-- Note, all arrays are zero-indexed (we assume this when
-- serializing/deserializing)
data ResolvedBCO
   = ResolvedBCO {
        resolvedBCOArity  :: {-# UNPACK #-} !Int,
        resolvedBCOInstrs :: UArray Int Word,           -- insns
        resolvedBCOBitmap :: UArray Int Word,           -- bitmap
        resolvedBCOLits   :: UArray Int Word,           -- non-ptrs
        resolvedBCOPtrs   :: (SizedSeq ResolvedBCOPtr)  -- ptrs
   }
   deriving (Generic, Show)

instance Binary ResolvedBCO where
  put ResolvedBCO{..} = do
    put resolvedBCOArity
    putArray resolvedBCOInstrs
    putArray resolvedBCOBitmap
    putArray resolvedBCOLits
    put resolvedBCOPtrs
  get = ResolvedBCO <$> get <*> getArray <*> getArray <*> getArray <*> get

data ResolvedBCOPtr
  = ResolvedBCORef {-# UNPACK #-} !Int
      -- ^ reference to the Nth BCO in the current set
  | ResolvedBCOPtr {-# UNPACK #-} !(RemoteRef HValue)
      -- ^ reference to a previously created BCO
  | ResolvedBCOStaticPtr {-# UNPACK #-} !(RemotePtr ())
      -- ^ reference to a static ptr
  | ResolvedBCOPtrBCO ResolvedBCO
      -- ^ a nested BCO
  | ResolvedBCOPtrBreakArray {-# UNPACK #-} !(RemoteRef BreakArray)
      -- ^ Resolves to the MutableArray# inside the BreakArray
  deriving (Generic, Show)

instance Binary ResolvedBCOPtr
