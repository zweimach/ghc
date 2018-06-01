module NonDetFV () where

import GhcPrelude

-- | A non-deterministic free-variable set.
--
-- The most common use of this is to compute in-scope sets.
--
-- This is a simplification of 'FV.FV':
--
--  * According to RAE we only need to filter the set for CoVars in one place
--    and otherwise have no need for other forms of filtering, so we drop the
--    'FV.InterestingVarFun'.
--
-- Generally it is necessary to eta-expand 'NonDetFV' computations for the
-- unfortunate reasons described in Note [FV eta expansion].
type NonDetFV = VarSet
                -- Locally bound variables
             -> VarSet
                -- Accumulator
             -> VarSet
                -- The resulting free-variable set.


-- | Run a free variable computation, returning a list of distinct free
-- variables in deterministic order and a non-deterministic set containing
-- those variables.
ndfvVarListVarSet :: FV ->  ([Var], VarSet)
ndfvfvVarListVarSet fv = fv (const True) emptyVarSet ([], emptyVarSet)

-- | Run a free variable computation, returning a list of distinct free
-- variables in deterministic order.
ndfvVarList :: FV -> [Var]
ndfvVarList = fst . ndfvVarListVarSet

-- | Run a free variable computation, returning a deterministic set of free
-- variables. Note that this is just a wrapper around the version that
-- returns a deterministic list. If you need a list you should use
-- `fvVarList`.
ndfvDVarSet :: FV -> DVarSet
ndfvDVarSet = mkDVarSet . fst . ndfvVarListVarSet

-- | Run a free variable computation, returning a non-deterministic set of
-- free variables. Don't use if the set will be later converted to a list
-- and the order of that list will impact the generated code.
ndfvVarSet :: FV -> VarSet
ndfvVarSet = snd . fvVarListVarSet

-- | Add a variable - when free, to the returned free variables.
-- Ignores duplicates and respects the filtering function.
unitNDFV :: Id -> NonDetFV
unitNDFV var in_scope acc@(have, haveSet)
  | var `elemVarSet` in_scope = acc
  | var `elemVarSet` haveSet = acc
  | otherwise = (var:have, extendVarSet haveSet var)
{-# INLINE unitNDFV #-}

-- | Return no free variables.
emptyFV :: NonDetFV
emptyFV _ acc = acc
{-# INLINE emptyNDFV #-}

-- | Union two free variable computations.
unionFV :: NonDetFV -> NonDetFV -> NonDetFV
unionFV fv1 fv2 in_scope acc =
  fv1 in_scope $! fv2 in_scope $! acc
{-# INLINE unionNDFV #-}

-- | Mark the variable as not free by putting it in scope.
delNDFV :: Var -> NonDetFV -> NonDetFV
delNDFV var fv !in_scope acc =
  fv (extendVarSet in_scope var) acc
{-# INLINE delNDFV #-}

-- | Mark many free variables as not free.
delNDFVs :: VarSet -> NonDetFV -> NonDetFV
delNDFVs vars fv !in_scope acc =
  fv (in_scope `unionVarSet` vars) acc
{-# INLINE delNDFVs #-}

-- | Map a free variable computation over a list and union the results.
mapUnionNDFV :: (a -> NonDetFV) -> [a] -> NonDetFV
mapUnionNDFV _f [] __in_scope acc = acc
mapUnionNDFV f (a:as) in_scope acc =
  mapUnionNDFV f as in_scope $! f a in_scope $! acc
{-# INLINABLE mapUnionNDFV #-}

-- | Union many free variable computations.
unionsFV :: [NonDetFV] -> NonDetFV
unionsFV fvs in_scope acc = mapUnionNDFV id fvs in_scope acc
{-# INLINE unionsNDFV #-}

-- | Add multiple variables - when free, to the returned free variables.
-- Ignores duplicates.
mkFVs :: [Var] -> NonDetFV
mkFVs vars in_scope acc =
  mapUnionNDFV unitNDFV vars in_scope acc
{-# INLINE mkNDFVs #-}
