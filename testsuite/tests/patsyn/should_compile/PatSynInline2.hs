{-# LANGUAGE PatternSynonyms #-}

module PatSynInline2 where

pattern Just' x = Just x
{-# INLINE Just' #-}
