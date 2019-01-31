{-# OPTIONS_GHC -fdefer-type-errors -fdefer-typed-holes  #-}
{-# OPTIONS_GHC -fdefer-out-of-scope-variables -Wno-typed-holes #-}
{-# OPTIONS_GHC -fplugin Simple.ExprTypePlugin #-}
{-# LANGUAGE LambdaCase, TypeApplications, MultiWayIf, TemplateHaskell #-}

module A where

data Point a = Point { x :: a, y :: a }

test1 :: Char -- type of expression constrained by type signature
test1 = if 1 == 1 then 'a' else 'b'
 -- type of expression without type signature
test2 = if 1 == 1 then 'a' else 'b'
 -- more complex if expression
test3 = if 1 == 1 then (1,2,3) else (4,5,6)
 -- case expression
test4 a = case a of "aaa" -> "bbb"
                    _     -> "aaa"
 -- let expression
test5 = let x = 3 in x + 4
 -- simple lambda expression
test6 = \() -> ()
 -- lambda case expression
test7 = \case [] -> "x"
              [a] -> a
 -- check that the type will be figured out from partial constraints
test8 x = if 1 == 1 then \_ -> []
                    else \_ -> fmap (const 'a') x
 -- function application
test9 = map (+1) [1..10]
 -- numeric literal
test10 = 3
 -- character literal
test11 = 'c'
 -- list literal
test12 = [1,2,3]
 -- constructor expression
test13 :: Point String
test13 = Point { x = "1", y = "2" }
 -- record update expression
test14 = test13 { x = 'x', y = 'y' }
 -- left operator section
test15 = (+ 3)
 -- right operator section
test16 = (4 :)
 -- tuple expression
test17 = (1,'c',"dfhakjf")
 -- operator application expression
test18 = 1 + 2
 -- type application expression
test19 = fmap @[]
 -- interval expression
test20 = [1..10]
 -- expression with type signature
test21 = 3 :: Int
 -- hole expression
test22 = 3 + _
 -- selector application
test23 = x test14
 -- negative prefix expression
test24 = -3
 -- multi way if expression
test25 = if | 1==1 -> 1
            | 2==2 -> 2
 -- do notation
test26 = do putStrLn "a"
            putStrLn "b"
 -- quote expression
test27 = [| 1 + 2 |]
 -- check that coerced type is used for variable
test28 :: Int
test28 = test29
 -- check that polymorphic coerced type is used for variable
test29 :: Num a => a
test29 = 3
