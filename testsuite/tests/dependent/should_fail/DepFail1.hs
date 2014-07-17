{-# LANGUAGE PolyKinds #-}

module DepFail1 where

data Proxy k (a :: k) = P

z :: Proxy Bool
z = P
