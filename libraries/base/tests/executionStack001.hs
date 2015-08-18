module Main where

import GHC.ExecutionStack
import System.IO.Unsafe (unsafePerformIO)
import Data.List(isInfixOf)

main :: IO()
main = do print 1
          print (judgeIfStackTracesWorks
                  (putMeOnStack
                    (unsafePerformIO getStackString)))
          print 2

getStackString :: IO String
getStackString = fmap showStackFrames currentStackFrames

{-# NOINLINE putMeOnStack #-}
putMeOnStack :: String -> String
putMeOnStack x = case x of
                   "hello" -> "world"
                   x       -> x

judgeIfStackTracesWorks :: String -> Bool
judgeIfStackTracesWorks = ("putMeOnStack" `isInfixOf`)
