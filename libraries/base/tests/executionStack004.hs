import GHC.ExecutionStack.Internal
import Data.List (isInfixOf)

-- In this test we check loading and unloading of codemap

main :: IO ()
main = do
    codemapTryUnload >>= (check . not) -- Starts unloaded
    _frames <- currentStackFrames
    codemapTryUnload >>= check  -- Unload successful
    codemapTryUnload >>= (check . not)  -- Already unloaded
    codemapTryUnload >>= (check . not)  -- Already unloaded

check :: Bool -> IO ()
check True  = putStrLn "OK"
check False = putStrLn "Not OK"
