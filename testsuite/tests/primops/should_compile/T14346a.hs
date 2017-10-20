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
    forkIO $ do
        -- With a compiler affected by #14346 this program would
        -- produce output of stdout. We run in a thread since the bug requires
        -- `forever` to reproduce.
        allocaBytes 4 $ \p ->
          forever $ do
            poke p (0xDEADBEEF :: Word32)
            threadDelay 10
            x <- peek p
            -- if things are working properly the result should always be
            -- 0xdeadbeef
            unless (x == 0xDEADBEEF) $ putStrLn (showHex x "")

    -- wait a few seconds to ensure we have a chance to reproduce the issue
    threadDelay $ 1000*1000*10
