{-# LANGUAGE DataKinds #-}

import Data.Typeable
import GHC.Types

-- Test that Typeable's kind representations work for various types.
-- See, for instance, #11120.

main :: IO ()
main = do
  print $ kindOf "hello world"
  print $ kindOf '4'
  print $ kindOf (42 :: Int)
  print $ kindOf (42 :: Word)
  print $ kindOf (3.1415 :: Double)
  print $ kindOf (return () :: IO ())
  print $ kindOf ('a', 1::Int, "hello")
  print $ kindOf (typeOf "hi")
  print $ kindOf True
  print $ kindOf EQ
  print $ kindOf (id :: Int -> Int)

  print $ kindOf (Proxy :: Proxy (Eq Int))
  print $ kindOf (Proxy :: Proxy (Int, Int))
  print $ kindOf (Proxy :: Proxy "hello world")
  print $ kindOf (Proxy :: Proxy 1)
  print $ kindOf (Proxy :: Proxy [1,2,3])
  print $ kindOf (Proxy :: Proxy 'EQ)
  print $ kindOf (Proxy :: Proxy TYPE)
  print $ kindOf (Proxy :: Proxy (TYPE 'Lifted))
  print $ kindOf (Proxy :: Proxy *)
  print $ kindOf (Proxy :: Proxy ★)
  print $ kindOf (Proxy :: Proxy 'Lifted)
  print $ kindOf (Proxy :: Proxy (~~))

kindOf :: forall a. Typeable a => a -> TypeRep
kindOf _ = kindRep (Proxy :: Proxy a)
