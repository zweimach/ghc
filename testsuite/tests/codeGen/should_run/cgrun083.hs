{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -msse #-}
{-# OPTIONS_GHC -msse2 #-}
{-# OPTIONS_GHC -msse4 #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
-- tests for SSE based vector load/stores operations

import GHC.Exts
import GHC.IO

data FloatX4  = FX4# FloatX4#

instance Show FloatX4 where
  show (FX4# f) = case (unpackFloatX4# f) of
    (# a, b, c, d #) -> show ((F# a), (F# b), (F# c), (F# d))


instance Eq FloatX4 where
  (FX4# a) == (FX4# b)
    = case (unpackFloatX4# a) of
        (# a1, a2, a3, a4 #) ->
          case (unpackFloatX4# b) of
            (# b1, b2, b3, b4 #) -> (F# a1) == (F# b1) &&
                                    (F# a2) == (F# b2) &&
                                    (F# a3) == (F# b3) &&
                                    (F# a4) == (F# b4)

data DoubleX2 = DX2# DoubleX2#

instance Show DoubleX2 where
  show (DX2# d) = case (unpackDoubleX2# d) of
    (# a, b #) -> show ((D# a), (D# b))


instance Eq DoubleX2 where
  (DX2# a) == (DX2# b)
    = case (unpackDoubleX2# a) of
        (# a1, a2 #) ->
          case (unpackDoubleX2# b) of
            (# b1, b2 #) -> (D# a1) == (D# b1) &&
                            (D# a2) == (D# b2)

writeFloatArray :: MutableByteArray RealWorld -> Int -> Float -> IO ()
writeFloatArray ba (I# i) (F# n) = IO $ \s ->
    case writeFloatArray# ba i n of s' -> (# s', () #)

readFloatX4 :: MutableByteArray RealWorld -> Int -> IO FloatX4
readFloatX4 ba (I# i) = IO $ \s ->
    case realFloatArrayAsFloatX4# ba i s of (# s', r #) -> (# s', FX4# r #)

writeDoubleArray :: MutableByteArray RealWorld -> Int -> Double -> IO ()
writeDoubleArray ba (I# i) (D# n) = IO $ \s ->
    case writeDoubleArray# ba i n of s' -> (# s', () #)

readFloatX4 :: MutableByteArray RealWorld -> Int -> IO DoubleX4
readFloatX4 ba (I# i) = IO $ \s ->
    case realDoubleArrayAsFloatX4# ba i s of (# s', r #) -> (# s', DX4# r #)

main :: IO ()
main = do
    ba <- IO $ \s -> case newAlignedPinnedByteArray# 64# 64# s of (# s', ba #) -> (# s', BA ba #)
    mapM_ (\i -> writeFloatArray ba i (realToFrac i + realToFrac i / 10)) [0..16]
    print $ readFloatX4 ba 0

    mapM_ (\i -> writeDoubleArray ba i (realToFrac i + realToFrac i / 10)) [0..8]
    print $ readDoubleX4 ba 0
