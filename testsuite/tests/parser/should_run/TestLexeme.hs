import Lexeme

import Data.Monoid

with :: a -> [a -> IO ()] -> IO ()
with x fs = mapM_ ($ x) fs

assert :: (String -> Bool) -> String -> IO ()
assert f a = do
  let res
        | f a  = "ok"
        | True = "fail"
  putStrLn $ a <>" "<>res

main :: IO ()
main = do
  with "Hello"
    [ assert isLexDataCon
    , assert isLexTyCon
    , assert $ not . isLexDataConSym
    , assert $ not . isLexTyConSym
    , assert $ not . isLexVarId
    ]

  with "hello"
    [ assert $ not . isLexDataCon
    , assert $ not . isLexTyCon
    , assert $ not . isLexVarSym
    , assert isLexVar
    ]

  with "%"
    [ assert $ not . isLexTyConId
    , assert $ not . isLexDataConId
    , assert $ not . isLexVarId
    , assert isLexTyCon
    , assert isLexDataCon
    , assert isLexVar
    ]

  with ":"
    [ assert $ not . isLexTyConId
    , assert $ not . isLexDataConId
    , assert $ not . isLexVarId
    , assert isLexTyCon
    , assert isLexDataCon
    , assert isLexVar
    ]

  with ":%"
    [ assert $ not . isLexTyConId
    , assert $ not . isLexDataConId
    , assert $ not . isLexVarId
    , assert isLexTyCon
    , assert isLexDataCon
    , assert isLexVar
    ]

  with "$dDict[]"
    [ assert $ not . isLexTyCon
    , assert $ not . isLexDataCon
    , assert $ not . isLexVarSym
    , assert isLexVar
    ]
