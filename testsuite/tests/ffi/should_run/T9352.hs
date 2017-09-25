{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

import GHC.Prim
import GHC.IO

foreign import ccall "hello"
    hello :: Int -> State# RealWorld -> State# RealWorld

main :: IO ()
main = do
    IO $ \s -> case hello 42 s of s' -> (# s', () #)
