
module GHC.ExecutionStack.ZDecode (decode) where

import Data.Char (isDigit, chr, ord)
import Numeric (readDec, readHex)

-- | Takes the digits of a hexadecimal number (starting with 0 if the first
-- digit would otherwise be a-f)
takeNumber :: String -> Maybe (String, String)
takeNumber [] = Nothing
takeNumber s@(c:_)
  | isDigit c = Just $ break (not . isHexDigit) s
  | otherwise = Nothing
  where
    -- Lowercase only
    isHexDigit d = isDigit d || (fromIntegral (ord c - ord 'a')::Word) <= 5

-- | Decode a string encoded with GHC's Z-encoding convention.
-- See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Compiler/SymbolNames
decode :: String -> String
decode ('Z':rest)
  -- Tuples
  | Just (digits, 'T':rest') <- takeNumber rest =
    let [(n,"")] = readDec digits
        decoded = "(" ++ replicate (n-1) ',' ++ ")"
    in decoded ++ decode rest'

  -- Unboxed tuples
  | Just (digits, 'H':rest') <- takeNumber rest =
    let [(n,"")] = readDec digits
        decoded
          | n == 1    = "(# #)"
          | otherwise = "(#"++replicate (n-1) ','++"#)"
    in decoded ++ decode rest'

  | char:rest' <- rest =
    let decoded = case char of
                      'L' -> "("
                      'R' -> ")"
                      'M' -> "["
                      'N' -> "]"
                      'C' -> ":"
                      'Z' -> "Z"
                      c   -> error ("unknown Z-encoding Z"++[c])
    in decoded ++ decode rest'

decode ('z':rest)
  -- Unicode characters
  | Just (digits, 'U':rest') <- takeNumber rest =
    let [(n,"")] = readHex digits
    in chr n : decode rest'

  -- Other
  | char:rest' <- rest =
    let decoded = case char of
                      'a' -> "&"
                      'b' -> "|"
                      'c' -> "^"
                      'd' -> "$"
                      'e' -> "="
                      'g' -> ">"
                      'h' -> "#"
                      'i' -> "."
                      'l' -> "<"
                      'm' -> "-"
                      'n' -> "!"
                      'p' -> "+"
                      'q' -> "q"
                      'r' -> "\\"
                      's' -> "/"
                      't' -> "*"
                      'u' -> "_"
                      'v' -> "%"
                      'z' -> "z"
                      c   -> error ("unknown Z-encoding z"++[c])
    in decoded ++ decode rest'

-- non Z-encoded characters
decode (c:rest) = c : decode rest
decode [] = []

tests :: [(String, String)]
tests =
    [ ("Trak",     "Trak")
    , ("foo_wib",  "foozuwib")
    , (">",        "zg")
    , (">1",       "zg1")
    , ("foo#",     "foozh")
    , ("foo##",    "foozhzh")
    , ("foo##1",   "foozhzh1")
    , ("fooZ",     "fooZZ")
    , (":+",       "ZCzp")
    , ("()",       "Z0T")
    , ("(,,,,)",   "Z5T")
    , ("(# #)",    "Z1H")
    , ("(#,,,,#)", "Z5H")
    ]

test = filter (\(dec,enc) -> decode enc /= dec) tests
