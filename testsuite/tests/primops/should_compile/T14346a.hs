-- ghc -Wall -fforce-recomp -O1 Test.hs -threaded
module Main where

import Control.Concurrent
import Control.Monad
import Data.Word
import Foreign.Marshal.Alloc
import Foreign.Storable
import Numeric

main :: IO ()
main = do
    replicateM_ 49 $ threadDelay 1
    allocaBytes 4 $ \p ->
      forever $ do
        poke p (0xDEADBEEF :: Word32)
        threadDelay 10
        x <- peek p
        unless (x == 0xDEADBEEF) $ putStrLn (showHex x "")
