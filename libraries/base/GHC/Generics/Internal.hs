{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE Trustworthy            #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

module GHC.Generics.Internal where

import GHC.Types
import Data.Proxy   ( Proxy(..) )
import GHC.TypeLits ( Nat, Symbol, KnownSymbol, KnownNat, symbolVal, natVal )
import GHC.Arr      ( Ix )
import GHC.Base     ( Functor, )
import GHC.Classes  ( Eq(..), Ord(..) )
import GHC.Enum     ( Bounded, Enum )
import Data.Maybe   ( Maybe(..) )
import GHC.Read     ( Read(..), lex, readParen )
import GHC.Show     ( Show(..), showString )

-- | Void: used for datatypes without constructors
data V1 (p :: k)
  deriving (Functor, Generic, Generic1)

-- | Unit: used for constructors without arguments
data U1 (p :: k) = U1
  deriving (Generic, Generic1)

-- | Used for marking occurrences of the parameter
newtype Par1 p = Par1 { unPar1 :: p }
  deriving (Eq, Ord, Read, Show, Functor, Generic, Generic1)

-- | Recursive calls of kind @* -> *@ (or kind @k -> *@, when @PolyKinds@
-- is enabled)
newtype Rec1 (f :: k -> *) (p :: k) = Rec1 { unRec1 :: f p }
  deriving (Eq, Ord, Read, Show, Functor, Generic, Generic1)

-- | Constants, additional parameters and recursion of kind @*@
newtype K1 (i :: *) c (p :: k) = K1 { unK1 :: c }
  deriving (Eq, Ord, Read, Show, Functor, Generic, Generic1)

-- | Meta-information (constructor names, etc.)
newtype M1 (i :: *) (c :: Meta) (f :: k -> *) (p :: k) = M1 { unM1 :: f p }
  deriving (Eq, Ord, Read, Show, Functor, Generic, Generic1)

-- | Sums: encode choice between constructors
infixr 5 :+:
data (:+:) (f :: k -> *) (g :: k -> *) (p :: k) = L1 (f p) | R1 (g p)
  deriving (Eq, Ord, Read, Show, Functor, Generic, Generic1)

-- | Products: encode multiple arguments to constructors
infixr 6 :*:
data (:*:) (f :: k -> *) (g :: k -> *) (p :: k) = f p :*: g p
  deriving (Eq, Ord, Read, Show, Functor, Generic, Generic1)

-- | Composition of functors
infixr 7 :.:
newtype (:.:) (f :: k2 -> *) (g :: k1 -> k2) (p :: k1) =
    Comp1 { unComp1 :: f (g p) }
  deriving (Eq, Ord, Read, Show, Functor, Generic, Generic1)

-- | Constants of unlifted kinds
--
-- @since 4.9.0.0
data family URec (a :: *) (p :: k)

-- | Datatype to represent the associativity of a constructor
data Associativity = LeftAssociative
                   | RightAssociative
                   | NotAssociative
  deriving (Eq, Show, Ord, Read, Enum, Bounded, Ix, Generic)

-- | The unpackedness of a field as the user wrote it in the source code. For
-- example, in the following data type:
--
-- @
-- data E = ExampleConstructor     Int
--            {\-\# NOUNPACK \#-\} Int
--            {\-\#   UNPACK \#-\} Int
-- @
--
-- The fields of @ExampleConstructor@ have 'NoSourceUnpackedness',
-- 'SourceNoUnpack', and 'SourceUnpack', respectively.
--
-- @since 4.9.0.0
data SourceUnpackedness = NoSourceUnpackedness
                        | SourceNoUnpack
                        | SourceUnpack
  deriving (Eq, Show, Ord, Read, Enum, Bounded, Ix, Generic)

-- | The strictness of a field as the user wrote it in the source code. For
-- example, in the following data type:
--
-- @
-- data E = ExampleConstructor Int ~Int !Int
-- @
--
-- The fields of @ExampleConstructor@ have 'NoSourceStrictness',
-- 'SourceLazy', and 'SourceStrict', respectively.
--
-- @since 4.9.0.0
data SourceStrictness = NoSourceStrictness
                      | SourceLazy
                      | SourceStrict
  deriving (Eq, Show, Ord, Read, Enum, Bounded, Ix, Generic)

-- | The strictness that GHC infers for a field during compilation. Whereas
-- there are nine different combinations of 'SourceUnpackedness' and
-- 'SourceStrictness', the strictness that GHC decides will ultimately be one
-- of lazy, strict, or unpacked. What GHC decides is affected both by what the
-- user writes in the source code and by GHC flags. As an example, consider
-- this data type:
--
-- @
-- data E = ExampleConstructor {\-\# UNPACK \#-\} !Int !Int Int
-- @
--
-- * If compiled without optimization or other language extensions, then the
--   fields of @ExampleConstructor@ will have 'DecidedStrict', 'DecidedStrict',
--   and 'DecidedLazy', respectively.
--
-- * If compiled with @-XStrictData@ enabled, then the fields will have
--   'DecidedStrict', 'DecidedStrict', and 'DecidedStrict', respectively.
--
-- * If compiled with @-O2@ enabled, then the fields will have 'DecidedUnpack',
--   'DecidedStrict', and 'DecidedLazy', respectively.
--
-- @since 4.9.0.0
data DecidedStrictness = DecidedLazy
                       | DecidedStrict
                       | DecidedUnpack
  deriving (Eq, Show, Ord, Read, Enum, Bounded, Ix, Generic)

-- | Representable types of kind *.
-- This class is derivable in GHC with the DeriveGeneric flag on.
class Generic a where
  -- | Generic representation type
  type Rep a :: * -> *
  -- | Convert from the datatype to its representation
  from  :: a -> (Rep a) x
  -- | Convert from the representation to the datatype
  to    :: (Rep a) x -> a


-- | Representable types of kind @* -> *@ (or kind @k -> *@, when @PolyKinds@
-- is enabled).
-- This class is derivable in GHC with the @DeriveGeneric@ flag on.
class Generic1 (f :: k -> *) where
  -- | Generic representation type
  type Rep1 f :: k -> *
  -- | Convert from the datatype to its representation
  from1  :: f a -> (Rep1 f) a
  -- | Convert from the representation to the datatype
  to1    :: (Rep1 f) a -> f a

--------------------------------------------------------------------------------
-- Meta-data
--------------------------------------------------------------------------------

-- | Datatype to represent metadata associated with a datatype (@MetaData@),
-- constructor (@MetaCons@), or field selector (@MetaSel@).
--
-- * In @MetaData n m p nt@, @n@ is the datatype's name, @m@ is the module in
--   which the datatype is defined, @p@ is the package in which the datatype
--   is defined, and @nt@ is @'True@ if the datatype is a @newtype@.
--
-- * In @MetaCons n f s@, @n@ is the constructor's name, @f@ is its fixity,
--   and @s@ is @'True@ if the constructor contains record selectors.
--
-- * In @MetaSel mn su ss ds@, if the field is uses record syntax, then @mn@ is
--   'Just' the record name. Otherwise, @mn@ is 'Nothing'. @su@ and @ss@ are
--   the field's unpackedness and strictness annotations, and @ds@ is the
--   strictness that GHC infers for the field.
--
-- @since 4.9.0.0
data Meta = MetaData Symbol Symbol Symbol Bool
          | MetaCons Symbol FixityI Bool
          | MetaSel  (Maybe Symbol)
                     SourceUnpackedness SourceStrictness DecidedStrictness

-- | This variant of 'Fixity' appears at the type level.
--
-- @since 4.9.0.0
data FixityI = PrefixI | InfixI Associativity Nat
