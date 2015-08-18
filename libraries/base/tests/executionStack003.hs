import GHC.ExecutionStack.Internal
import Data.List (isInfixOf)
import Control.Concurrent.MVar (MVar, newEmptyMVar, takeMVar, putMVar)
import Control.Concurrent (forkIO)

-- In this test checks thread safety, which means that a thread can't unload
-- the codemap data while another thread is in an `withCodemap` block.

-- Can the thread executing this access codemap (load it before you call)
checkCanAccessCodemap :: IO Bool
checkCanAccessCodemap = do
    frames <- currentExecutionStack >>= getStackFramesNoSync
    return $ any frameHasData frames
  where
    frameHasData = not . ("Data not found" `isInfixOf`) . procedureName

main :: IO ()
main = do
    var1 <- newEmptyMVar
    var2 <- newEmptyMVar
    putStrLn "1"
    codemapIsLoaded >>= (check . not)
    checkCanAccessCodemap >>= (check . not)
    codemapTryUnload >>= (check . not)
    _thread <- forkIO $ do
        takeMVar var1
        -- When doing the codemapIsLoaded check here, we also verify that other
        -- threads can access the codemap info. But I'm not sure how to test
        -- that a different unix thread can access the codemap info as well.
        putStrLn "3"
        codemapIsLoaded >>= check
        checkCanAccessCodemap >>= check
        codemapTryUnload >>= (check . not)
        codemapIsLoaded >>= check
        putMVar var2 ()
    withCodemap $ do
        putStrLn "2"
        codemapIsLoaded >>= check
        codemapTryUnload >>= (check . not)
        putMVar var1 ()
        takeMVar var2
    putStrLn "4"
    withCodemap $ return ()
    codemapIsLoaded >>= check
    codemapTryUnload >>= check


check :: Bool -> IO ()
check True  = putStrLn "OK"
check False = putStrLn "Not OK"
