{-# LANGUAGE TemplateHaskell, TypeOperators #-}

module T10583 where

import Language.Haskell.TH

data a & b = Mk

$( do n <- lookupTypeName "&"
      runIO $ print n
      return [] )
