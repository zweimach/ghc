{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoImplicitPrelude #-}

module GHC.Fingerprint (
        fingerprintString,
        fingerprintFingerprints,
        fingerprintData
  ) where

import GHC.Base (String, Int, IO)
import GHC.Ptr (Ptr)
import GHC.Word (Word8)
import GHC.Fingerprint.Type (Fingerprint)

fingerprintFingerprints :: [Fingerprint] -> Fingerprint
fingerprintString :: String -> Fingerprint
fingerprintData :: Ptr Word8 -> Int -> IO Fingerprint
