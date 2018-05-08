{-# LANGUAGE CPP, DeriveDataTypeable #-}

module HsDoc (
  HsDocString(..),
  LHsDocString,
  ppr_mbDoc
  ) where

#include "HsVersions.h"

import GhcPrelude

import Binary
import Outputable
import SrcLoc
import FastString

import Data.Data

-- | Haskell Documentation String
newtype HsDocString = HsDocString FastString
  deriving (Eq, Show, Data)

instance Binary HsDocString where
  put_ bh (HsDocString s) = put_ bh s
  get bh = HsDocString <$> get bh

-- | Located Haskell Documentation String
type LHsDocString = Located HsDocString

instance Outputable HsDocString where
  ppr (HsDocString fs) = ftext fs

ppr_mbDoc :: Maybe LHsDocString -> SDoc
ppr_mbDoc (Just doc) = ppr doc
ppr_mbDoc Nothing    = empty

