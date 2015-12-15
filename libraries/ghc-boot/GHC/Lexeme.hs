-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Lexeme
-- Copyright   :  (c) The GHC Team
--
-- Maintainer  :  ghc-devs@haskell.org
-- Portability :  portable
--
-- Functions to evaluate whether or not a string is a valid identifier.
--
module GHC.Lexeme (
          -- * Lexical characteristics of Haskell names
        isSpecial, startsVarSym, startsVarId, startsDataConSym,
        startsTyConSym, startsDataConId, startsTyConId
  ) where

import Data.Char

isSpecial, startsVarSym, startsDataConSym, startsTyConSym,
  startsVarId, startsDataConId, startsTyConId :: Char -> Bool

-- | The @special@ character class as defined by Section 2.2 of the Haskell 2010
-- Report.
isSpecial c = c `elem` "(),;[]`{}"
-- This should remain is sync with the $special character set in Lexer.x

startsVarSym c =
  (isPunctuation c || isSymbol c)
  && c `notElem` ":_\"'"
  && not (isSpecial c)

startsDataConSym = startsTyConSym     -- Infix data constructors

startsTyConSym c                      -- Infix type constructors
  | c == ':'  = True
  | otherwise = (isPunctuation c || isSymbol c) &&
                not ((c `elem` "_\"'") || isSpecial c)


startsVarId c  = c == '_' || case generalCategory c of  -- Ordinary Ids
  LowercaseLetter -> True
  OtherLetter     -> True   -- See #1103
  _               -> False

startsDataConId c = c == '(' || case generalCategory c of
  UppercaseLetter -> True
  _               -> False

startsTyConId = startsDataConId
