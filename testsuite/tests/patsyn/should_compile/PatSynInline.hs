module PatSynInline where

import PatSynInline2

hello :: Maybe Int -> Int
hello (Just' x) = x
hello _         = 42
