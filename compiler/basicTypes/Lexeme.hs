-- (c) The GHC Team
--
-- Functions to evaluate whether or not a string is a valid identifier.
-- There is considerable overlap between the logic here and the logic
-- in Lexer.x, but sadly there seems to be way to merge them.

module Lexeme (
        -- * Classifying names

        -- | Use these functions to figure what kind of name a 'String'
        -- might represent. These functions only /classify/ a lexeme; they are
        -- necessary but not sufficient conditions for the /validity/
        -- of the lexeme. For the latter see the functions in the Validating
        -- identifiers section of this module.
        isLexDataCon, isLexTyCon, isLexVar,
        -- ** Testing for identifiers
        isLexTyConId, isLexDataConId, isLexVarId, isLexTyVarId,
        -- ** Testing for symbols
        isLexTyConSym, isLexDataConSym, isLexVarSym, isLexTyVarSym,

        -- ** Character predicates
        isSpecial,
        startsVarSym, startsVarId, startsDataConSym, startsTyConSym,
        startsDataConId,

        -- * Validating identifiers

        -- | These functions (working over plain old 'String's) check
        -- to make sure that the identifier is valid.
        okVarOcc, okDataConOcc, okTyVarOcc, okTyConOcc,
        okVarIdOcc, okVarSymOcc, okDataConIdOcc, okTyConIdOcc,
        okDataConSymOcc, okTyConSymOcc

        -- Some of the exports above are not used within GHC, but may
        -- be of value to GHC API users.
  ) where

import Util ((<||>))

import Data.Char
import qualified Data.Set as Set

import GHC.Lexeme

{-

************************************************************************
*                                                                      *
    Lexical categories
*                                                                      *
************************************************************************

These functions test strings to see if they fit the lexical categories
defined in the Haskell report.

Note [Classification of generated names]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Some names generated for internal use can show up in debugging output,
e.g.  when using -ddump-simpl. These generated names start with a $
but should still be pretty-printed using prefix notation. We make sure
this is the case in isLexVarSym by only classifying a name as a symbol
if its first two characters are symbols, not just its first one.
-}

-- | Is a lexeme a valid data constructor name?
isLexDataCon :: String -> Bool
isLexDataCon cs =
  isLexConId cs || isLexDataConSym cs

-- | Is a lexeme a valid type constructor name?
isLexTyCon :: String -> Bool
isLexTyCon cs =
  isLexConId cs || isLexTyConSym cs

-- | Is a lexeme a valid term-level variable name?
isLexVar :: String -> Bool
isLexVar cs =
  isLexVarId cs || isLexVarSym cs

-- this function is not exported
-- | Is a lexeme a valid data or type constructor which can be used in
-- prefix position?
-- e.g. @Foo@, @[]@, and @(,)@
isLexConId :: String -> Bool
isLexConId ""          = False
isLexConId "[]"        = True
isLexConId (c:_)       = startsDataConId c

-- | Is a lexeme possibly a valid data constructor which can be used in prefix
-- position?
-- e.g. @Foo@
isLexTypeConId :: String -> Bool
isLexTypeConId         = isLexConId

-- | Is a lexeme possibly a valid data constructor which can be used in prefix
-- position?
-- e.g. @Foo@
isLexDataConId :: String -> Bool
isLexDataConId         = isLexConId

-- | Is a lexeme a valid non-symbol type variable?
isLexTyVarId :: String -> Bool
isLexTyVarId = isLexVarId

-- | Is a lexeme a valid term-level identifier which can be used in prefix
-- position?
-- e.g. @x@ and @_x@
isLexVarId :: String -> Bool
isLexVarId ""          = False
isLexVarId (c:_)       = startsVarId c

-- | Is a lexeme a valid type constructor which can be used in infix position?
-- e.g. @:-:@, @:@, @->@, and @+@
isLexTyConSym :: String -> Bool
isLexTyConSym ""       = False
isLexTyConSym "->"     = True
isLexTyConSym (c:_)    = startsTyConSym c

-- | Is a lexeme a valid data constructor which can be used in infix position?
-- e.g. @:-:@ and @:@
isLexDataConSym :: String -> Bool
isLexDataConSym ""     = False
isLexDataConSym "->"   = True
isLexDataConSym cs     = startsDataConSym (head cs)
  -- See note [Classification of generated names]

-- | Is a lexeme a valid term-level identifier which can be used in
-- infix position?
-- e.g. @+@
isLexVarSym :: String -> Bool
isLexVarSym ""         = False
isLexVarSym "~R#"      = True
isLexVarSym (c:cs)
  | startsVarSym c     = null cs || okSymChar (head cs)
    -- See note [Classification of generated names]
  | otherwise          = False

-- | Is a lexeme a valid type variable which can be used in infix position?
-- There are no examples.
isLexTyVarSym :: String -> Bool
isLexTyVarSym _ = False   -- no symbols are type variables.

{-

************************************************************************
*                                                                      *
    Detecting valid names for Template Haskell
*                                                                      *
************************************************************************

-}

----------------------
-- External interface
----------------------

-- | Is this an acceptable variable name?
okVarOcc :: String -> Bool
okVarOcc str@(c:_)
  | startsVarId c
  = okVarIdOcc str
  | startsVarSym c
  = okVarSymOcc str
okVarOcc _ = False

-- | Is this an acceptable data constructor name?
okDataConOcc :: String -> Bool
okDataConOcc str@(c:_)
  | startsDataConId c
  = okDataConIdOcc str
  | startsDataConSym c
  = okDataConSymOcc str
  | str == "[]"
  = True
okDataConOcc _ = False

-- | Is this an acceptable type variable name?
okTyVarOcc :: String -> Bool
okTyVarOcc = okIdOcc

-- | Is this an acceptable type constructor name?
okTyConOcc :: String -> Bool
okTyConOcc "[]" = True
okTyConOcc "->" = True
okTyConOcc "~"  = True
okTyConOcc str@(c:_)
  | startsTyConId c
  = okTyConIdOcc str
  | startsTyConSym c
  = okTyConSymOcc str
okTyConOcc _ = False

-- | Is this an acceptable alphanumeric variable name, assuming it starts
-- with an acceptable letter?
okVarIdOcc :: String -> Bool
okVarIdOcc str = okIdOcc str &&
                 -- admit "_" as a valid identifier.  Required to support typed
                 -- holes in Template Haskell.  See #10267
                 (str == "_" || not (str `Set.member` reservedIds))

-- | Is this an acceptable symbolic variable name, assuming it starts
-- with an acceptable character?
okVarSymOcc :: String -> Bool
okVarSymOcc str = all okSymChar str &&
                  not (str `Set.member` reservedOps) &&
                  not (isDashes str)

-- | Is this an acceptable alphanumeric data constructor name, assuming it
-- starts with an acceptable letter?
okDataConIdOcc :: String -> Bool
okDataConIdOcc str = okIdOcc str ||
                 is_tuple_name1 str
  where
    -- check for tuple name, starting at the beginning
    is_tuple_name1 ('(' : rest) = is_tuple_name2 rest
    is_tuple_name1 _            = False

    -- check for tuple tail
    is_tuple_name2 ")"          = True
    is_tuple_name2 (',' : rest) = is_tuple_name2 rest
    is_tuple_name2 (ws  : rest)
      | isSpace ws              = is_tuple_name2 rest
    is_tuple_name2 _            = False

-- | Is this an acceptable alphanumeric type constructor name, assuming it
-- starts with an acceptable character?
okTyConIdOcc :: String -> Bool
okTyConIdOcc = okDataConIdOcc

-- | Is this an acceptable symbolic data constructor name, assuming it
-- starts with an acceptable character?
okDataConSymOcc :: String -> Bool
okDataConSymOcc ":" = True
okDataConSymOcc str = all okSymChar str &&
                  not (str `Set.member` reservedOps)

-- | Is this an acceptable symbolic type constructor name, assuming it
-- starts with an acceptable character?
okTyConSymOcc :: String -> Bool
okTyConSymOcc str = all okSymChar str &&
                  not (str `Set.member` reservedOps)

----------------------
-- Internal functions
----------------------

-- | Is this string an acceptable id, possibly with a suffix of hashes,
-- but not worrying about case or clashing with reserved words?
okIdOcc :: String -> Bool
okIdOcc str
  -- TODO. #10196. Only allow modifier letters in the suffix of an identifier.
  = let hashes = dropWhile (okIdChar <||> okIdSuffixChar) str in
    all (== '#') hashes   -- -XMagicHash allows a suffix of hashes
                          -- of course, `all` says "True" to an empty list

-- | Is this character acceptable in an identifier (after the first letter)?
-- See 'alexGetByte' in @Lexer.x@
okIdChar :: Char -> Bool
okIdChar c = case generalCategory c of
  UppercaseLetter -> True
  LowercaseLetter -> True
  OtherLetter     -> True
  TitlecaseLetter -> True
  DecimalNumber   -> True
  OtherNumber     -> True
  _               -> c == '\'' || c == '_'

-- | Is this character acceptable in the suffix of an identifier.
-- See 'alexGetByte' in @Lexer.x@
okIdSuffixChar :: Char -> Bool
okIdSuffixChar c = case generalCategory c of
  ModifierLetter  -> True  -- See #10196
  _               -> False

-- | Is this character acceptable in a symbol (after the first char)?
-- See 'alexGetByte' in @Lexer.x@
okSymChar :: Char -> Bool
okSymChar c
  | isSpecial c
  = False
  | c `elem` "_\"'"
  = False
  | otherwise
  = case generalCategory c of
      ConnectorPunctuation -> True
      DashPunctuation      -> True
      OtherPunctuation     -> True
      MathSymbol           -> True
      CurrencySymbol       -> True
      ModifierSymbol       -> True
      OtherSymbol          -> True
      _                    -> False

-- | All reserved identifiers. Taken from section 2.4 of the 2010 Report.
reservedIds :: Set.Set String
reservedIds = Set.fromList [ "case", "class", "data", "default", "deriving"
                           , "do", "else", "foreign", "if", "import", "in"
                           , "infix", "infixl", "infixr", "instance", "let"
                           , "module", "newtype", "of", "then", "type", "where"
                           , "_" ]

-- | All reserved operators. Taken from section 2.4 of the 2010 Report.
reservedOps :: Set.Set String
reservedOps = Set.fromList [ "..", ":", "::", "=", "\\", "|", "<-", "->"
                           , "@", "~", "=>" ]

-- | Does this string contain only dashes and has at least 2 of them?
isDashes :: String -> Bool
isDashes ('-' : '-' : rest) = all (== '-') rest
isDashes _                  = False
