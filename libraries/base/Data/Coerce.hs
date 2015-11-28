{-# LANGUAGE Unsafe                #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE RoleAnnotations       #-}
{-# LANGUAGE IncoherentInstances   #-}  -- needed for the role annot. on a class

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Coerce
-- Copyright   :  (c) The University of Glasgow 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- Safe coercions between data types.
--
-- More in-depth information can be found on the
-- <https://ghc.haskell.org/trac/ghc/wiki/Roles Roles wiki page>
--
-- @since 4.7.0.0
-----------------------------------------------------------------------------

module Data.Coerce
        ( -- * Safe coercions
          coerce, Coercible, HCoercible
        ) where

import GHC.Prim (coerce#)
import GHC.Types (HCoercible)

-- We probably should depend on GHC.Base here (see Note [Depend on GHC.Integer]
-- and Note [Depend on GHC.Tuple] in that file), but this module is so simple,
-- we can get away without doing so. (Specifically, no literals or tuples.)

-- | This two-parameter class has instances for types @a@ and @b@ if
--      the compiler can infer that they have the same representation. This class
--      does not have regular instances; instead they are created on-the-fly during
--      type-checking. Trying to manually declare an instance of @Coercible@
--      is an error.
--
--      Nevertheless one can pretend that the following three kinds of instances
--      exist. First, as a trivial base-case:
--
--      @instance a a@
--
--      Furthermore, for every type constructor there is
--      an instance that allows to coerce under the type constructor. For
--      example, let @D@ be a prototypical type constructor (@data@ or
--      @newtype@) with three type arguments, which have roles @nominal@,
--      @representational@ resp. @phantom@. Then there is an instance of
--      the form
--
--      @instance Coercible b b\' => Coercible (D a b c) (D a b\' c\')@
--
--      Note that the @nominal@ type arguments are equal, the
--      @representational@ type arguments can differ, but need to have a
--      @Coercible@ instance themself, and the @phantom@ type arguments can be
--      changed arbitrarily.
--
--      The third kind of instance exists for every @newtype NT = MkNT T@ and
--      comes in two variants, namely
--
--      @instance Coercible a T => Coercible a NT@
--
--      @instance Coercible T b => Coercible NT b@
--
--      This instance is only usable if the constructor @MkNT@ is in scope.
--
--      If, as a library author of a type constructor like @Set a@, you
--      want to prevent a user of your module to write
--      @coerce :: Set T -> Set NT@,
--      you need to set the role of @Set@\'s type parameter to @nominal@,
--      by writing
--
--      @type role Set nominal@
--
--      For more details about this feature, please refer to
--      <http://www.cis.upenn.edu/~eir/papers/2014/coercible/coercible.pdf Safe Coercions>
--      by Joachim Breitner, Richard A. Eisenberg, Simon Peyton Jones and Stephanie Weirich.
--
--      @since 4.7.0.0
class HCoercible a b => Coercible (a :: k) (b :: k)
instance HCoercible a b => Coercible a b
type role Coercible representational representational

-- | The function 'coerce' allows you to safely convert between values of
--     types that have the same representation with no run-time overhead. In the
--   simplest case you can use it instead of a newtype constructor, to go from
--   the newtype's concrete type to the abstract type. But it also works in
--   more complicated settings, e.g. converting a list of newtypes to a list of
--   concrete types.
coerce :: Coercible a b => a -> b
coerce = coerce#
{-# NOINLINE [0] coerce #-} -- allow rules like "map/coerce" to fire.
