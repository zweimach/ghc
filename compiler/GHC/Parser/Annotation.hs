{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module GHC.Parser.Annotation (
  -- getAnnotation, getAndRemoveAnnotation,
  -- getAnnotationComments,getAndRemoveAnnotationComments,
  ApiAnns(..),
  ApiAnnKey,
  AnnKeywordId(..),
  AnnotationComment(..),
  IsUnicodeSyntax(..),
  unicodeAnn,
  HasE(..),
  LRdrName, -- Exists for haddocks only

  -- * In-tree Api Annotations
  LocatedA, LocatedL, LocatedC, LocatedN, LocatedAn, LocatedP,

  SrcSpanAnnA, SrcSpanAnnL, SrcSpanAnnP, SrcSpanAnnC, SrcSpanAnnName, SrcSpanAnn'(..),
  AddApiAnn(..),
  ApiAnn, ApiAnn'(..),
  ApiAnnCO, ApiAnnComments,
  noAnn,

  AnnsModule(..),
  AnnListItem(..), AnnList(..), AnnParen(..), ParenType(..),
  AnnPragma(..),
  AnnContext(..),
  AnnSortKey(..),
  NameAnn(..), NameAdornment(..),
  NoApiAnns(..),

  addCLocA, addCLocAA,
  combineLocsA, sortLocatedA,
  noLocA, getLocA, getLocAnn,
  noSrcSpanA,
  mapLocA, reAnn,
  noAnnSrcSpan, noComments, comment,
  addAnns, addAnnsA,
  apiAnnAnns, apiAnnAnnsL, apiAnnComments,
  annParen2AddApiAnn, parenTypeKws,
  realSrcSpan,
  la2na, na2la, n2l, l2n, l2l, la2la,
  combineSrcSpansA,
  reLocL, reLoc, reLocA, reLocN,
  TrailingAnn(..), addTrailingAnnToA, addTrailingAnnToL, addTrailingCommaToN,
  placeholderRealSpan,
  reAnnL, reAnnC,
  extraToAnnList
  ) where

import GHC.Prelude

import Data.Data
import Data.Function (on)
import Data.List (sortBy)
-- import qualified Data.Map as Map
import Data.Semigroup
import GHC.Data.FastString
import GHC.Types.Name.Reader
import GHC.Types.SrcLoc
import GHC.Utils.Binary
import GHC.Utils.Outputable hiding ( (<>) )

{-
Note [Api annotations]
~~~~~~~~~~~~~~~~~~~~~~
Given a parse tree of a Haskell module, how can we reconstruct
the original Haskell source code, retaining all whitespace and
source code comments?  We need to track the locations of all
elements from the original source: this includes keywords such as
'let' / 'in' / 'do' etc as well as punctuation such as commas and
braces, and also comments.  We collectively refer to this
metadata as the "API annotations".

Rather than annotate the resulting parse tree with these locations
directly (this would be a major change to some fairly core data
structures in GHC), we instead capture locations for these elements in a
structure separate from the parse tree, and returned in the
pm_annotations field of the ParsedModule type.

The full ApiAnns type is

> data ApiAnns =
>  ApiAnns
>    { apiAnnItems :: Map.Map ApiAnnKey [RealSrcSpan],
>      apiAnnEofPos :: Maybe RealSrcSpan,
>      apiAnnComments :: Map.Map RealSrcSpan [RealLocated AnnotationComment],
>      apiAnnRogueComments :: [RealLocated AnnotationComment]
>    }

NON-COMMENT ELEMENTS

Intuitively, every AST element directly contains a bag of keywords
(keywords can show up more than once in a node: a semicolon i.e. newline
can show up multiple times before the next AST element), each of which
needs to be associated with its location in the original source code.

Consequently, the structure that records non-comment elements is logically
a two level map, from the RealSrcSpan of the AST element containing it, to
a map from keywords ('AnnKeyWord') to all locations of the keyword directly
in the AST element:

> type ApiAnnKey = (RealSrcSpan,AnnKeywordId)
>
> Map.Map ApiAnnKey [RealSrcSpan]

So

> let x = 1 in 2 *x

would result in the AST element

  L span (HsLet (binds for x = 1) (2 * x))

and the annotations

  (span,AnnLet) having the location of the 'let' keyword
  (span,AnnEqual) having the location of the '=' sign
  (span,AnnIn)  having the location of the 'in' keyword

For any given element in the AST, there is only a set number of
keywords that are applicable for it (e.g., you'll never see an
'import' keyword associated with a let-binding.)  The set of allowed
keywords is documented in a comment associated with the constructor
of a given AST element, although the ground truth is in GHC.Parser
and GHC.Parser.PostProcess (which actually add the annotations; see #13012).

COMMENT ELEMENTS

Every comment is associated with a *located* AnnotationComment.
We associate comments with the lowest (most specific) AST element
enclosing them:

> Map.Map RealSrcSpan [RealLocated AnnotationComment]

PARSER STATE

There are three fields in PState (the parser state) which play a role
with annotations.

>  annotations :: [(ApiAnnKey,[RealSrcSpan])],
>  comment_q :: [RealLocated AnnotationComment],
>  annotations_comments :: [(RealSrcSpan,[RealLocated AnnotationComment])]

The 'annotations' and 'annotations_comments' fields are simple: they simply
accumulate annotations that will end up in 'ApiAnns' at the end
(after they are passed to Map.fromList).

The 'comment_q' field captures comments as they are seen in the token stream,
so that when they are ready to be allocated via the parser they are
available (at the time we lex a comment, we don't know what the enclosing
AST node of it is, so we can't associate it with a RealSrcSpan in
annotations_comments).

PARSER EMISSION OF ANNOTATIONS

The parser interacts with the lexer using the function

> addAnnotation :: RealSrcSpan -> AnnKeywordId -> RealSrcSpan -> P ()

which takes the AST element RealSrcSpan, the annotation keyword and the
target RealSrcSpan.

This adds the annotation to the `annotations` field of `PState` and
transfers any comments in `comment_q` WHICH ARE ENCLOSED by
the RealSrcSpan of this element to the `annotations_comments`
field.  (Comments which are outside of this annotation are deferred
until later. 'allocateComments' in 'Lexer' is responsible for
making sure we only attach comments that actually fit in the 'SrcSpan'.)

The wiki page describing this feature is
https://gitlab.haskell.org/ghc/ghc/wikis/api-annotations

-}
-- ---------------------------------------------------------------------

-- If you update this, update the Note [Api annotations] above
-- AZ:TODO ^^^ take note
data ApiAnns =
  ApiAnns
    { apiAnnEofPos :: Maybe RealSrcSpan,
      apiAnnRogueComments :: [RealLocated AnnotationComment]
    }

-- If you update this, update the Note [Api annotations] above
type ApiAnnKey = (RealSrcSpan,AnnKeywordId)


-- -- | Retrieve a list of annotation 'SrcSpan's based on the 'SrcSpan'
-- -- of the annotated AST element, and the known type of the annotation.
-- getAnnotation :: ApiAnns -> RealSrcSpan -> AnnKeywordId -> [RealSrcSpan]
-- getAnnotation anns span ann =
--   case Map.lookup ann_key ann_items of
--     Nothing -> []
--     Just ss -> ss
--   where ann_items = apiAnnItems anns
--         ann_key = (span,ann)

-- -- | Retrieve a list of annotation 'SrcSpan's based on the 'SrcSpan'
-- -- of the annotated AST element, and the known type of the annotation.
-- -- The list is removed from the annotations.
-- getAndRemoveAnnotation :: ApiAnns -> RealSrcSpan -> AnnKeywordId
--                        -> ([RealSrcSpan],ApiAnns)
-- getAndRemoveAnnotation anns span ann =
--   case Map.lookup ann_key ann_items of
--     Nothing -> ([],anns)
--     Just ss -> (ss,anns{ apiAnnItems = Map.delete ann_key ann_items })
--   where ann_items = apiAnnItems anns
--         ann_key = (span,ann)

-- |Retrieve the comments allocated to the current 'SrcSpan'
--
-- --  Note: A given 'SrcSpan' may appear in multiple AST elements,
-- --  beware of duplicates
-- getAnnotationComments :: ApiAnns -> RealSrcSpan -> [RealLocated AnnotationComment]
-- getAnnotationComments anns span =
--   case Map.lookup span (apiAnnComments anns) of
--     Just cs -> cs
--     Nothing -> []

-- -- |Retrieve the comments allocated to the current 'SrcSpan', and
-- -- remove them from the annotations
-- getAndRemoveAnnotationComments :: ApiAnns -> RealSrcSpan
--                                -> ([RealLocated AnnotationComment],ApiAnns)
-- getAndRemoveAnnotationComments anns span =
--   case Map.lookup span ann_comments of
--     Just cs -> (cs, anns{ apiAnnComments = Map.delete span ann_comments })
--     Nothing -> ([], anns)
--   where ann_comments = apiAnnComments anns

-- --------------------------------------------------------------------

-- | API Annotations exist so that tools can perform source to source
-- conversions of Haskell code. They are used to keep track of the
-- various syntactic keywords that are not captured in the existing
-- AST.
--
-- The annotations, together with original source comments are made
-- available in the @'pm_annotations'@ field of @'GHC.ParsedModule'@.
-- Comments are only retained if @'Opt_KeepRawTokenStream'@ is set in
-- @'GHC.Driver.Session.DynFlags'@ before parsing.
--
-- The wiki page describing this feature is
-- https://gitlab.haskell.org/ghc/ghc/wikis/api-annotations
--
-- Note: in general the names of these are taken from the
-- corresponding token, unless otherwise noted
-- See note [Api annotations] above for details of the usage
data AnnKeywordId
    = AnnAnyclass
    | AnnAs
    | AnnAt
    | AnnBang  -- ^ '!'
    | AnnBackquote -- ^ '`'
    | AnnBy
    | AnnCase -- ^ case or lambda case
    | AnnClass
    | AnnClose -- ^  '\#)' or '\#-}'  etc
    | AnnCloseB -- ^ '|)'
    | AnnCloseBU -- ^ '|)', unicode variant
    | AnnCloseC -- ^ '}'
    | AnnCloseQ  -- ^ '|]'
    | AnnCloseQU -- ^ '|]', unicode variant
    | AnnCloseP -- ^ ')'
    | AnnClosePH -- ^ '\#)'
    | AnnCloseS -- ^ ']'
    | AnnColon
    | AnnComma -- ^ as a list separator
    | AnnCommaTuple -- ^ in a RdrName for a tuple
    | AnnDarrow -- ^ '=>'
    | AnnDarrowU -- ^ '=>', unicode variant
    | AnnData
    | AnnDcolon -- ^ '::'
    | AnnDcolonU -- ^ '::', unicode variant
    | AnnDefault
    | AnnDeriving
    | AnnDo
    | AnnDot    -- ^ '.'
    | AnnDotdot -- ^ '..'
    | AnnElse
    | AnnEqual
    | AnnExport
    | AnnFamily
    | AnnForall
    | AnnForallU -- ^ Unicode variant
    | AnnForeign
    | AnnFunId -- ^ for function name in matches where there are
               -- multiple equations for the function.
    | AnnGroup
    | AnnHeader -- ^ for CType
    | AnnHiding
    | AnnIf
    | AnnImport
    | AnnIn
    | AnnInfix -- ^ 'infix' or 'infixl' or 'infixr'
    | AnnInstance
    | AnnLam
    | AnnLarrow     -- ^ '<-'
    | AnnLarrowU    -- ^ '<-', unicode variant
    | AnnLet
    | AnnLolly  -- ^ '#->'
    | AnnLollyU -- ^ '#->', unicode variant
    | AnnMdo
    | AnnMinus -- ^ '-'
    | AnnModule
    | AnnNewtype
    | AnnName -- ^ where a name loses its location in the AST, this carries it
    | AnnOf
    | AnnOpen    -- ^ '{-\# LANGUAGE' etc
    | AnnOpenB   -- ^ '(|'
    | AnnOpenBU  -- ^ '(|', unicode variant
    | AnnOpenC   -- ^ '{'
    | AnnOpenE   -- ^ '[e|' or '[e||'
    | AnnOpenEQ  -- ^ '[|'
    | AnnOpenEQU -- ^ '[|', unicode variant
    | AnnOpenP   -- ^ '('
    | AnnOpenS   -- ^ '['
    | AnnOpenPH  -- ^ '(\#'
    | AnnDollar          -- ^ prefix '$'   -- TemplateHaskell
    | AnnDollarDollar    -- ^ prefix '$$'  -- TemplateHaskell
    | AnnPackageName
    | AnnPattern
    | AnnProc
    | AnnQualified
    | AnnRarrow -- ^ '->'
    | AnnRarrowU -- ^ '->', unicode variant
    | AnnRec
    | AnnRole
    | AnnSafe
    | AnnSemi -- ^ ';'
    | AnnSimpleQuote -- ^ '''
    | AnnSignature
    | AnnStatic -- ^ 'static'
    | AnnStock
    | AnnThen
    | AnnThTyQuote -- ^ double '''
    | AnnTilde -- ^ '~'
    | AnnType
    | AnnUnit -- ^ '()' for types
    | AnnUsing
    | AnnVal  -- ^ e.g. INTEGER
    | AnnValStr  -- ^ String value, will need quotes when output
    | AnnVbar -- ^ '|'
    | AnnVia -- ^ 'via'
    | AnnWhere
    | Annlarrowtail -- ^ '-<'
    | AnnlarrowtailU -- ^ '-<', unicode variant
    | Annrarrowtail -- ^ '->'
    | AnnrarrowtailU -- ^ '->', unicode variant
    | AnnLarrowtail -- ^ '-<<'
    | AnnLarrowtailU -- ^ '-<<', unicode variant
    | AnnRarrowtail -- ^ '>>-'
    | AnnRarrowtailU -- ^ '>>-', unicode variant
    deriving (Eq, Ord, Data, Show)

instance Outputable AnnKeywordId where
  ppr x = text (show x)

-- ---------------------------------------------------------------------

data AnnotationComment =
  -- Documentation annotations
    AnnDocCommentNext  String     -- ^ something beginning '-- |'
  | AnnDocCommentPrev  String     -- ^ something beginning '-- ^'
  | AnnDocCommentNamed String     -- ^ something beginning '-- $'
  | AnnDocSection      Int String -- ^ a section heading
  | AnnDocOptions      String     -- ^ doc options (prune, ignore-exports, etc)
  | AnnLineComment     String     -- ^ comment starting by "--"
  | AnnBlockComment    String     -- ^ comment in {- -}
    deriving (Eq, Ord, Data, Show)
-- Note: these are based on the Token versions, but the Token type is
-- defined in GHC.Parser.Lexer and bringing it in here would create a loop

instance Outputable AnnotationComment where
  ppr x = text (show x)

-- | - 'GHC.Parser.Annotation.AnnKeywordId' : 'GHC.Parser.Annotation.AnnOpen',
--             'GHC.Parser.Annotation.AnnClose','GHC.Parser.Annotation.AnnComma',
--             'GHC.Parser.Annotation.AnnRarrow'
--             'GHC.Parser.Annotation.AnnTilde'
--   - May have 'GHC.Parser.Annotation.AnnComma' when in a list
type LRdrName = Located RdrName


-- | Certain tokens can have alternate representations when unicode syntax is
-- enabled. This flag is attached to those tokens in the lexer so that the
-- original source representation can be reproduced in the corresponding
-- 'ApiAnnotation'
data IsUnicodeSyntax = UnicodeSyntax | NormalSyntax
    deriving (Eq, Ord, Data, Show)

-- | Convert a normal annotation into its unicode equivalent one
unicodeAnn :: AnnKeywordId -> AnnKeywordId
unicodeAnn AnnForall     = AnnForallU
unicodeAnn AnnDcolon     = AnnDcolonU
unicodeAnn AnnLarrow     = AnnLarrowU
unicodeAnn AnnRarrow     = AnnRarrowU
unicodeAnn AnnDarrow     = AnnDarrowU
unicodeAnn Annlarrowtail = AnnlarrowtailU
unicodeAnn Annrarrowtail = AnnrarrowtailU
unicodeAnn AnnLarrowtail = AnnLarrowtailU
unicodeAnn AnnRarrowtail = AnnRarrowtailU
unicodeAnn AnnOpenB      = AnnOpenBU
unicodeAnn AnnCloseB     = AnnCloseBU
unicodeAnn AnnOpenEQ     = AnnOpenEQU
unicodeAnn AnnCloseQ     = AnnCloseQU
unicodeAnn AnnLolly      = AnnLollyU
unicodeAnn ann           = ann


-- | Some template haskell tokens have two variants, one with an `e` the other
-- not:
--
-- >  [| or [e|
-- >  [|| or [e||
--
-- This type indicates whether the 'e' is present or not.
data HasE = HasE | NoE
     deriving (Eq, Ord, Data, Show)

-- ---------------------------------------------------------------------

-- | Encapsulated call to addAnnotation, requiring only the SrcSpan of
--   the AST construct the annotation belongs to; together with the
--   AnnKeywordId, this is the key of the annotation map.
--
--   This type is useful for places in the parser where it is not yet
--   known what SrcSpan an annotation should be added to.  The most
--   common situation is when we are parsing a list: the annotations
--   need to be associated with the AST element that *contains* the
--   list, not the list itself.  'AddApiAnn' lets us defer adding the
--   annotations until we finish parsing the list and are now parsing
--   the enclosing element; we then apply the 'AddApiAnn' to associate
--   the annotations.  Another common situation is where a common fragment of
--   the AST has been factored out but there is no separate AST node for
--   this fragment (this occurs in class and data declarations). In this
--   case, the annotation belongs to the parent data declaration.
--
--   The usual way an 'AddApiAnn' is created is using the 'mj' ("make jump")
--   function, and then it can be discharged using the 'ams' function.
data AddApiAnn = AddApiAnn AnnKeywordId RealSrcSpan deriving (Data,Show,Eq)

instance Outputable AddApiAnn where
  ppr (AddApiAnn kw ss) = text "AddApiAnn" <+> ppr kw <+> ppr ss

data TrailingAnn
  = AddSemiAnn RealSrcSpan
  | AddCommaAnn RealSrcSpan
  | AddVbarAnn RealSrcSpan
  | AddRarrowAnn RealSrcSpan
  | AddRarrowAnnU RealSrcSpan
  | AddLollyAnn RealSrcSpan
  | AddLollyAnnU RealSrcSpan
  deriving (Data,Show,Eq, Ord)

instance Outputable TrailingAnn where
  ppr (AddSemiAnn ss)    = text "AddSemiAnn"    <+> ppr ss
  ppr (AddCommaAnn ss)   = text "AddCommaAnn"   <+> ppr ss
  ppr (AddVbarAnn ss)    = text "AddVbarAnn"    <+> ppr ss
  ppr (AddRarrowAnn ss)  = text "AddRarrowAnn"  <+> ppr ss
  ppr (AddRarrowAnnU ss) = text "AddRarrowAnnU" <+> ppr ss
  ppr (AddLollyAnn ss)   = text "AddLollyAnn"   <+> ppr ss
  ppr (AddLollyAnnU ss)  = text "AddLollyAnnU"  <+> ppr ss

-- ---------------------------------------------------------------------

{-
Note [In-tree Api annotations]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Rather than being loosely coupled to the ParsedSource via the location
of the AST fragment the annotation pertains to, they are now encoded
directly into the HsSyn AST via the TTG extension points for GhcPs.

In order to do this in a type safe way the following data types are
defined.
-}


-- | The API Annotations are now kept in the HsSyn AST for the GhcPs
--   phase. We do not always have API Annotations though, only for
--   parsed code. This type captures that, and allows the
--   representation decision to be easily revisited as it evolves.
--
-- A goal of the annotations is that an AST can be edited, including
-- moving subtrees from one place to another, duplicating them, and so
-- on.  This means that each fragment must be self-contained.  To this
-- end, each annotated fragment keeps track of the anchor position it
-- was originally captured at, being simply the start span of the
-- topmost element of the ast fragment.  This gives us a way to later
-- re-calculate all Located items in this layer of the AST, as well as
-- any annotations captured. The comments associated with the AST
-- fragment are also captured here.
--
-- We capture the location of a sub-element here, within a given
-- sub-element it has its own anchor used to calculate relative
-- positions, so it means the sub-elements can be relocated, or new
-- ones synthesised and inserted without hardship.
--
-- The ann type parameter allows this general structure to be
-- specialised to the specific set of locations of original
-- AnnKeywordId elements. Note: we may reduce the usage of
-- AnnKeywordId, and use locations only, as captured in that
-- structure.
data ApiAnn' ann
  = ApiAnn { anchor   :: RealSrcSpan -- ^ Base location for the start of
                                     -- the syntactic element holding the
                                     -- annotations.
           , anns     :: ann -- ^ Annotations added by the Parser
           , comments :: [RealLocated AnnotationComment]
              -- ^ Comments enclosed in the SrcSpan of the element
              -- this `ApiAnn'` is attached to
           }
  | ApiAnnNotUsed -- ^ No Annotation for generated code,
                                 -- e.g. from TH, deriving, etc.
        deriving (Data, Eq, Functor)

type ApiAnn = ApiAnn' [AddApiAnn]
type ApiAnnComments = [RealLocated AnnotationComment]

data NoApiAnns = NoApiAnns
  deriving (Data,Eq,Ord)

type ApiAnnCO = ApiAnn' NoApiAnns -- ^ Api Annotations for comments only

noComments ::ApiAnnCO
noComments = ApiAnn placeholderRealSpan NoApiAnns []

placeholderRealSpan :: RealSrcSpan
placeholderRealSpan = realSrcLocSpan (mkRealSrcLoc (mkFastString "placeholder") 0 0)

comment :: RealSrcSpan -> ApiAnnComments -> ApiAnnCO
comment loc cs = ApiAnn loc NoApiAnns cs

type LocatedA = GenLocated SrcSpanAnnA
type LocatedL = GenLocated SrcSpanAnnL
type LocatedP = GenLocated SrcSpanAnnP
type LocatedC = GenLocated SrcSpanAnnC
type LocatedN = GenLocated SrcSpanAnnName

type LocatedAn an = GenLocated (SrcSpanAnn' (ApiAnn' an))

type SrcSpanAnnA = SrcSpanAnn' (ApiAnn' AnnListItem)
type SrcSpanAnnL = SrcSpanAnn' (ApiAnn' AnnList)
type SrcSpanAnnP = SrcSpanAnn' (ApiAnn' AnnPragma)
type SrcSpanAnnC = SrcSpanAnn' (ApiAnn' AnnContext)
type SrcSpanAnnName = SrcSpanAnn' (ApiAnn' NameAnn)

data SrcSpanAnn' a = SrcSpanAnn { ann :: a, locA :: SrcSpan }
        deriving (Data, Eq)

instance (Outputable a) => Outputable (SrcSpanAnn' a) where
  ppr (SrcSpanAnn a l) = text "SrcSpanAnn" <+> ppr a <+> ppr l

instance (Outputable a, Outputable e)
     => Outputable (GenLocated (SrcSpanAnn' a) e) where
  ppr = pprLocated

instance Outputable AnnListItem where
  ppr (AnnListItem ts) = text "AnnListItem" <+> ppr ts

instance Outputable NameAdornment where
  ppr NameParens     = text "NameParens"
  ppr NameParensHash = text "NameParensHash"
  ppr NameBackquotes = text "NameBackquotes"
  ppr NameSquare     = text "NameSquare"

instance Outputable NameAnn where
  ppr (NameAnn a o n c t)
    = text "NameAnn" <+> ppr a <+> ppr o <+> ppr n <+> ppr c <+> ppr t
  ppr (NameAnnCommas a o n c t)
    = text "NameAnnCommas" <+> ppr a <+> ppr o <+> ppr n <+> ppr c <+> ppr t
  ppr (NameAnnOnly a o c t)
    = text "NameAnnOnly" <+> ppr a <+> ppr o <+> ppr c <+> ppr t
  ppr (NameAnnRArrow n t)
    = text "NameAnnRArrow" <+> ppr n <+> ppr t
  ppr (NameAnnQuote q n t)
    = text "NameAnnQuote" <+> ppr q <+> ppr n <+> ppr t
  ppr (NameAnnTrailing t)
    = text "NameAnnTrailing" <+> ppr t

instance Outputable AnnList where
  ppr (AnnList o c r t) = text "AnnList" <+> ppr o <+> ppr c <+> ppr r <+> ppr t

instance Outputable AnnPragma where
  ppr (AnnPragma o c r) = text "AnnPragma" <+> ppr o <+> ppr c <+> ppr r

-- sortLocatedA :: [LocatedA a] -> [LocatedA a]
sortLocatedA :: [GenLocated (SrcSpanAnn' a) e] -> [GenLocated (SrcSpanAnn' a) e]
sortLocatedA = sortBy (leftmost_smallest `on` getLocA)

mapLocA :: (a -> b) -> GenLocated SrcSpan a -> GenLocated (SrcSpanAnn' (ApiAnn' ann)) b
mapLocA f (L l a) = L (noAnnSrcSpan l) (f a)

-- AZ:TODO: move this somewhere sane

-- combineLocsA :: LocatedA a -> LocatedA b -> SrcSpanAnn
combineLocsA :: Semigroup a => GenLocated (SrcSpanAnn' a) e1 -> GenLocated (SrcSpanAnn' a) e2 -> SrcSpanAnn' a
combineLocsA (L a _) (L b _) = combineSrcSpansA a b

-- combineSrcSpansA :: SrcSpanAnn -> SrcSpanAnn -> SrcSpanAnn
combineSrcSpansA :: Semigroup a => SrcSpanAnn' a -> SrcSpanAnn' a -> SrcSpanAnn' a
combineSrcSpansA (SrcSpanAnn aa la) (SrcSpanAnn ab lb)
  = SrcSpanAnn (aa <> ab) (combineSrcSpans la lb)

-- | Combine locations from two 'Located' things and add them to a third thing
-- addCLocA :: LocatedA a -> Located b -> c -> LocatedA c
addCLocA :: GenLocated (SrcSpanAnn' a) e1 -> GenLocated SrcSpan e2 -> e3 -> GenLocated (SrcSpanAnn' (ApiAnn' ann)) e3
addCLocA a b c = L (noAnnSrcSpan $ combineSrcSpans (locA $ getLoc a) (getLoc b)) c

-- addCLocAA :: LocatedA a -> LocatedA b -> c -> LocatedA c
addCLocAA :: GenLocated (SrcSpanAnn' a1) e1 -> GenLocated (SrcSpanAnn' a2) e2 -> e3 -> GenLocated (SrcSpanAnn' (ApiAnn' ann)) e3
addCLocAA a b c = L (noAnnSrcSpan $ combineSrcSpans (locA $ getLoc a) (locA $ getLoc b)) c

-- ---------------------------------------------------------------------

-- AZ: rename this, it is used in more than just HsModule
data AnnsModule
  = AnnsModule {
    am_main :: [AddApiAnn],
    am_decls :: AnnList
    } deriving (Data, Eq)

-- ---------------------------------------------------------------------
-- Annotations for lists of items
-- ---------------------------------------------------------------------

data AnnListItem
  = AnnListItem {
      lann_trailing  :: [TrailingAnn]
      }
  deriving (Data, Eq)

-- ---------------------------------------------------------------------
-- Managing annotations for lists
-- ---------------------------------------------------------------------

-- AZ:TODO: consider adding an AnnSortKey
data AnnList
  = AnnList {
      al_open      :: Maybe AddApiAnn,
      al_close     :: Maybe AddApiAnn,
      al_rest      :: [AddApiAnn],
      al_trailing  :: [TrailingAnn]
      } deriving (Data,Eq)

-- ---------------------------------------------------------------------

data AnnParen
  = AnnParen {
      ap_adornment :: ParenType,
      ap_open      :: RealSrcSpan,
      ap_close     :: RealSrcSpan
      } deriving (Data)

data ParenType
  = AnnParens
  | AnnParensHash
  | AnnParensSquare
  deriving (Eq, Ord, Data)

data AnnContext
  = AnnContext {
      ac_darrow    :: Maybe (IsUnicodeSyntax, RealSrcSpan),
      ac_open      :: [RealSrcSpan],
      ac_close     :: [RealSrcSpan]
      } deriving (Data)

-- | Captures the sort order of sub elements. This is needed when the
-- sub-elements have been split (as in a HsLocalBind which holds separate
-- binds and sigs) or for infix patterns where the order has been
-- re-arranged. It is captured explicitly so that after the Delta phase a
-- SrcSpan is used purely as an index into the annotations, allowing
-- transformations of the AST including the introduction of new Located
-- items or re-arranging existing ones.
data AnnSortKey
  = NoAnnSortKey
  | AnnSortKey [RealSrcSpan]
  deriving (Data)


-- ---------------------------------------------------------------------
-- Annotations for names
-- ---------------------------------------------------------------------
-- We initially wrapped all names in Located as a hook for the
-- annotations. Now we can do it directly


data NameAnn
  = NameAnn {
      nann_adornment :: NameAdornment,
      nann_open      :: RealSrcSpan,
      nann_name      :: RealSrcSpan,
      nann_close     :: RealSrcSpan,
      nann_trailing  :: [TrailingAnn]
      }
  | NameAnnCommas {
      nann_adornment :: NameAdornment,
      nann_open      :: RealSrcSpan,
      nann_commas    :: [RealSrcSpan],
      nann_close     :: RealSrcSpan,
      nann_trailing  :: [TrailingAnn]
      }
  | NameAnnOnly {
      nann_adornment :: NameAdornment,
      nann_open      :: RealSrcSpan,
      nann_close     :: RealSrcSpan,
      nann_trailing  :: [TrailingAnn]
      }
  | NameAnnRArrow {
      nann_name      :: RealSrcSpan,
      nann_trailing  :: [TrailingAnn]
      }
  | NameAnnQuote {
      nann_quote     :: RealSrcSpan,
      nann_quoted    :: ApiAnn' NameAnn,
      nann_trailing  :: [TrailingAnn]
      }
  | NameAnnTrailing {
      nann_trailing  :: [TrailingAnn]
      }
  deriving (Data, Eq)

data NameAdornment
  = NameParens
  | NameParensHash
  | NameBackquotes
  | NameSquare
  deriving (Eq, Ord, Data)
-- Annotations that can occur for a RdrName
--
--  AnnVal - when RdrName has adornments
--    AnnOpenP, AnnCloseP for '(' ')'
--    AnnBackquote '`' x 2
--    AnnOpenPH, AnnClosePH for '(#', '#)'
--    AnnOpenS, AnnCloseS for '[' ']'
-- AnnRarrow, AnnRarrowU for '->' or unicode version
--   with
--    AnnOpenP, AnnCloseP for '(' ')'

-- ---------------------------------------------------------------------

data AnnPragma
  = AnnPragma {
      apr_open      :: AddApiAnn,
      apr_close     :: AddApiAnn,
      apr_rest      :: [AddApiAnn]
      } deriving (Data,Eq)

-- ---------------------------------------------------------------------

addTrailingAnnToL :: SrcSpan -> TrailingAnn -> ApiAnnComments -> ApiAnn' AnnList -> ApiAnn' AnnList
addTrailingAnnToL s t cs ApiAnnNotUsed = ApiAnn (realSrcSpan s) (AnnList Nothing Nothing [] [t]) cs
addTrailingAnnToL _ t cs n = n { anns = addTrailing (anns n)
                               , comments = comments n ++ cs }
  where
    addTrailing n = n { al_trailing = t : al_trailing n }

addTrailingAnnToA :: SrcSpan -> TrailingAnn -> ApiAnnComments -> ApiAnn' AnnListItem -> ApiAnn' AnnListItem
addTrailingAnnToA s t cs ApiAnnNotUsed = ApiAnn (realSrcSpan s) (AnnListItem [t]) cs
addTrailingAnnToA _ t cs n = n { anns = addTrailing (anns n)
                               , comments = comments n ++ cs }
  where
    addTrailing n = n { lann_trailing = t : lann_trailing n }

addTrailingCommaToN :: SrcSpan -> ApiAnn' NameAnn -> RealSrcSpan -> ApiAnn' NameAnn
addTrailingCommaToN s ApiAnnNotUsed l = ApiAnn (realSrcSpan s) (NameAnnTrailing [AddCommaAnn l]) []
addTrailingCommaToN _ n l = n { anns = addTrailing (anns n) l }
  where
    addTrailing :: NameAnn -> RealSrcSpan -> NameAnn
    addTrailing n l = n { nann_trailing = AddCommaAnn l : nann_trailing n }

-- ---------------------------------------------------------------------

-- |Helper function (temporary) during transition of names
--  Discards any annotations
l2n :: LocatedAn a1 a2 -> LocatedN a2
l2n (L la a) = L (noAnnSrcSpan (locA la)) a

n2l :: LocatedN a -> LocatedA a
n2l (L la a) = L (na2la la) a

-- |Helper function (temporary) during transition of names
--  Discards any annotations
-- la2na :: SrcSpanAnn -> SrcSpanAnnName
la2na :: SrcSpanAnn' a -> SrcSpanAnnName
la2na l = noAnnSrcSpan (locA l)

-- |Helper function (temporary) during transition of names
--  Discards any annotations
la2la :: LocatedAn ann1 a2 -> LocatedAn ann2 a2
la2la (L la a) = L (noAnnSrcSpan (locA la)) a

-- l2l :: SrcSpanAnn' a -> SrcSpanAnn' b
l2l :: SrcSpanAnn' a -> SrcSpanAnn' (ApiAnn' ann)
l2l l = noAnnSrcSpan (locA l)

-- |Helper function (temporary) during transition of names
--  Discards any annotations
-- na2la :: SrcSpanAnnName -> SrcSpanAnn
na2la :: SrcSpanAnn' a -> SrcSpanAnn' (ApiAnn' ann)
na2la l = noAnnSrcSpan (locA l)

-- ---------------------------------------------------------------------

realSrcSpan :: SrcSpan -> RealSrcSpan
realSrcSpan (RealSrcSpan s _) = s
-- realSrcSpan _ = panic "expecting RealSrcSpan"
realSrcSpan _ = mkRealSrcSpan l l -- AZ temporary
  where
    l = mkRealSrcLoc (fsLit "foo") (-1) (-1)

extraToAnnList :: AnnList -> [AddApiAnn] -> AnnList
extraToAnnList (AnnList o c e t) as = AnnList o c (e++as) t

reAnn :: [TrailingAnn] -> ApiAnnComments -> Located a -> LocatedA a
reAnn anns cs (L l a) = L (SrcSpanAnn (ApiAnn (realSrcSpan l) (AnnListItem anns) cs) l) a

reAnnC :: AnnContext -> ApiAnnComments -> Located a -> LocatedC a
reAnnC anns cs (L l a) = L (SrcSpanAnn (ApiAnn (realSrcSpan l) anns cs) l) a

-- reAnnL :: AnnList -> ApiAnnComments -> Located a -> LocatedL a
reAnnL :: ann -> ApiAnnComments -> Located e -> GenLocated (SrcSpanAnn' (ApiAnn' ann)) e
reAnnL anns cs (L l a) = L (SrcSpanAnn (ApiAnn (realSrcSpan l) anns cs) l) a

noLocA :: a -> LocatedAn an a
noLocA = L (SrcSpanAnn ApiAnnNotUsed noSrcSpan)

getLocA :: GenLocated (SrcSpanAnn' a) e -> SrcSpan
getLocA (L (SrcSpanAnn _ l) _) = l

getLocAnn :: Located a  -> SrcSpanAnnA
getLocAnn (L l _) = SrcSpanAnn ApiAnnNotUsed l

noAnnSrcSpan :: SrcSpan -> SrcSpanAnn' (ApiAnn' ann)
noAnnSrcSpan l = SrcSpanAnn ApiAnnNotUsed l

noSrcSpanA :: SrcSpanAnn' (ApiAnn' ann)
noSrcSpanA = noAnnSrcSpan noSrcSpan

reLoc :: LocatedAn a e -> Located e
reLoc (L (SrcSpanAnn _ l) a) = L l a

reLocA :: Located e -> LocatedAn ann e
reLocA (L l a) = (L (SrcSpanAnn ApiAnnNotUsed l) a)

reLocL :: LocatedN e -> LocatedA e
reLocL (L l a) = (L (na2la l) a)

reLocN :: LocatedN a -> Located a
reLocN (L (SrcSpanAnn _ l) a) = L l a

noAnn :: ApiAnn' a
noAnn = ApiAnnNotUsed

-- TODO:AZ combining anchor locations needs to be done properly.  Or
-- this function discarded.
addAnns :: ApiAnn -> [AddApiAnn] -> ApiAnnComments -> ApiAnn
addAnns (ApiAnn l as1 cs) as2 cs2 = ApiAnn l (as1 ++ as2) (cs ++ cs2)
addAnns ApiAnnNotUsed [] [] = ApiAnnNotUsed
addAnns ApiAnnNotUsed as cs = ApiAnn placeholderRealSpan as cs

addAnnsA :: SrcSpanAnnA -> [TrailingAnn] -> ApiAnnComments -> SrcSpanAnnA
addAnnsA (SrcSpanAnn (ApiAnn l as1 cs) loc) as2 cs2
  = SrcSpanAnn (ApiAnn l (AnnListItem (lann_trailing as1 ++ as2)) (cs ++ cs2)) loc
addAnnsA (SrcSpanAnn ApiAnnNotUsed loc) [] []
  = SrcSpanAnn ApiAnnNotUsed loc
addAnnsA (SrcSpanAnn ApiAnnNotUsed loc) as cs
  = SrcSpanAnn (ApiAnn (realSrcSpan loc) (AnnListItem as) cs) loc

apiAnnAnnsL :: ApiAnn' a -> [a]
apiAnnAnnsL ApiAnnNotUsed = []
apiAnnAnnsL (ApiAnn _ anns _) = [anns]

apiAnnAnns :: ApiAnn -> [AddApiAnn]
apiAnnAnns ApiAnnNotUsed = []
apiAnnAnns (ApiAnn _ anns _) = anns

annParen2AddApiAnn :: ApiAnn' AnnParen -> [AddApiAnn]
annParen2AddApiAnn ApiAnnNotUsed = []
annParen2AddApiAnn (ApiAnn _ (AnnParen pt o c) _)
  = [AddApiAnn ai o, AddApiAnn ac c]
  where
    (ai,ac) = parenTypeKws pt

parenTypeKws :: ParenType -> (AnnKeywordId, AnnKeywordId)
parenTypeKws AnnParens       = (AnnOpenP, AnnCloseP)
parenTypeKws AnnParensHash   = (AnnOpenPH, AnnClosePH)
parenTypeKws AnnParensSquare = (AnnOpenS, AnnCloseS)


apiAnnComments :: ApiAnn' an -> ApiAnnComments
apiAnnComments ApiAnnNotUsed = []
apiAnnComments (ApiAnn _ _ cs) = cs

-- TODO:AZ combining anchor locations needs to be done properly.  Or
-- this function discarded.
instance (Semigroup a) => Semigroup (ApiAnn' a) where
  ApiAnnNotUsed <> x = x
  x <> ApiAnnNotUsed = x
  (ApiAnn l1 a1 b1) <> (ApiAnn l2 a2 b2) = ApiAnn l1 (a1 <> a2) (b1 <> b2)

instance (Monoid a) => Monoid (ApiAnn' a) where
  mempty = ApiAnnNotUsed

instance Semigroup AnnListItem where
  (AnnListItem l1) <> (AnnListItem l2) = AnnListItem (l1 <> l2)

instance (Outputable a) => Outputable (ApiAnn' a) where
  ppr (ApiAnn l a c)  = text "ApiAnn" <+> ppr l <+> ppr a <+> ppr c
  ppr ApiAnnNotUsed = text "ApiAnnNotUsed"


instance Outputable AnnContext where
  ppr (AnnContext a o c) = text "AnnContext" <+> ppr a <+> ppr o <+> ppr c

instance Outputable IsUnicodeSyntax where
  ppr = text . show

instance Binary a => Binary (LocatedL a) where
  -- We do not serialise the annotations
    put_ bh (L l x) = do
            put_ bh (locA l)
            put_ bh x

    get bh = do
            l <- get bh
            x <- get bh
            return (L (noAnnSrcSpan l) x)
