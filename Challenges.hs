-- Author: Diana-Alexandra Crintea
-- Student ID: 29572088
-- Date: 13/12/2018
-- COMP2209 Coursework 2, University of Southampton
-- (c) Copyright by the University of Southampton

-- This module statement makes public only the specified functions and types
module Challenges (convertLet, prettyPrint, parseLet, countReds, compileArith,
    Expr(App, Let, Var), LamExpr(LamApp, LamAbs, LamVar)) where

import Data.Char
import Parsing

-- Challenge 1
data Expr = App Expr Expr | Let [Int] Expr Expr | Var Int deriving (Show,Eq)
data LamExpr = LamApp LamExpr LamExpr | LamAbs Int LamExpr | LamVar Int deriving (Show,Eq)

-- get the type of the expression
getType :: Expr -> Int
getType (Let xs x y) = 0
getType (App x y) = 1
getType (Var i) = 2

-- get the variable
getVar :: Expr -> Int
getVar (Var i) = i

-- get the array
getArr :: Expr -> [Int]
getArr (Let xs x y) = xs

-- get inner expressions
getExpr :: Expr -> (Expr,Expr)
getExpr (Let xs x y) = (x,y)
getExpr (App x y) = (x,y)

-- convert let
cvt :: Expr -> LamExpr
cvt (Let [a] x y) = convertLet x
cvt (Let (a:as) x y) = (LamAbs (head as) (cvt (Let as x y)))

-- convert a let expression to lambda expression
convertLet :: Expr -> LamExpr
convertLet e  | getType e == 2 = (LamVar (getVar e))
              | getType e == 1 = (LamApp (convertLet (fst (getExpr e))) (convertLet (snd (getExpr e))))
              | getType e == 0 = (LamApp (LamAbs (head (getArr e)) (convertLet (snd (getExpr e)))) (cvt e))

-- Challenge 2

-- this funtion returns the elements in the array as a String
str :: [Int] -> String
str [] = ""
str (x:xs) = "x" ++ show x ++ " " ++ str xs

-- pretty print a let expression by converting it to a string
prettyPrint :: Expr -> String
prettyPrint e     | getType e == 0 = "let " ++ str (getArr e) ++ "= " ++ prettyPrint (fst (getExpr e)) ++ " in " ++ prettyPrint (snd (getExpr e))
                  | (getType e == 1) && (getType (fst (getExpr e)) == 0) && (getType (snd (getExpr e)) == 2) = "(" ++ prettyPrint (fst (getExpr e)) ++ ") " ++ prettyPrint (snd (getExpr e))
                  | (getType e == 1) && (getType (fst (getExpr e)) == 0) && (getType (snd (getExpr e)) /= 2) = "(" ++ prettyPrint (fst (getExpr e)) ++ ") (" ++ prettyPrint (snd (getExpr e)) ++ ")"
                  | (getType e == 1) && (getType (fst (getExpr e)) /= 0) && (getType (snd (getExpr e)) == 2) = prettyPrint (fst (getExpr e)) ++ " " ++ prettyPrint (snd (getExpr e))
                  | (getType e == 1) && (getType (fst (getExpr e)) /= 0) && (getType (snd (getExpr e)) /= 2) = prettyPrint (fst (getExpr e)) ++ " (" ++ prettyPrint (snd (getExpr e)) ++ ")"
                  | getType e == 2 = "x" ++ show (getVar e)

-- Challenge 3

-- definition vor the Var type of Expr
varExpr :: Parser Expr
varExpr = do  x <- char 'x'
              i <- nat
              return (Var i)

-- definition vor the Var type of Expr between paranthesis
varPExpr :: Parser Expr
varPExpr = do symbol "("
              x <- char 'x'
              i <- nat
              symbol ")"
              return (Var i)

-- definition of a let variable
var :: Parser Int
var = do  x <- char 'x'
          i <- nat
          return i

-- definition of the array of let variables

array :: Parser [Int]
array = do  xs <- many (token var)
            return xs

-- definition of the let expression
letExpr :: Parser Expr
letExpr = do  symbol "let"
              arr <- array
              symbol "="
              e1 <- expr
              symbol "in"
              e2 <- expr
              return (Let arr e1 e2)

-- definition of the app expression
appExpr :: Parser Expr
appExpr = do  e1 <- lowerExpr
              space
              e2 <- expr
              return (App e1 e2)

-- definition of the app expression that has both expressions variables
basicAppExpr :: Parser Expr
basicAppExpr = do e1 <- lowestExpr
                  space
                  e2 <- lowestExpr
                  return (App e1 e2)

-- definition of an expression surrounded in brackets
bracketsExpr :: Parser Expr
bracketsExpr = do symbol "("
                  e <- expr
                  symbol ")"
                  return e

-- definitions of the leveled entry points
expr :: Parser Expr
expr = appExpr <|> lowerExpr
lowerExpr = bracketsExpr <|> letExpr <|> basicAppExpr <|> lowestExpr
lowestExpr = varExpr

-- this function parses a given string
pLet :: String -> [(Expr,String)]
pLet s = parse expr s

-- this function returns Nothing if the input is invalid and Just E where E is the coresponding expression otherwise
parseLet :: String -> Maybe Expr
parseLet s   | length (pLet s) == 0 = Nothing
             | snd (head (pLet s)) /= "" = Nothing
             | otherwise = Just (fst (head (pLet s)))


-- Challenge 4

-- this funtion returns the type of the lambda function
getLamType :: LamExpr -> Int
getLamType (LamApp x y) = 0
getLamType (LamAbs i x) = 1
getLamType (LamVar i) = 2

-- this function returns the expressions from LamApp type
getAppExpr :: LamExpr -> (LamExpr,LamExpr)
getAppExpr (LamApp x y) = (x,y)

-- this function returns the expression from LamAbs type
getAbsExpr :: LamExpr -> LamExpr
getAbsExpr (LamAbs i x) = x

-- this function caluclates the number of reductions using the innermost leftmost reduction by counting the number of App expressions from left
countLeft :: LamExpr -> Int
countLeft e   | getLamType e == 0 = 1 + countLeft (fst (getAppExpr e))
              | getLamType e == 1 = countLeft (getAbsExpr e)
              | otherwise = 0

-- this function caluclates the number of reductions using the innermost rightmost reduction by counting all App expressions
countRight :: LamExpr -> Int
countRight e  | getLamType e == 0 = 1 + countRight (fst (getAppExpr e)) + countRight (snd (getAppExpr e))
              | getLamType e == 1 = countRight (getAbsExpr e)
              | getLamType e == 2 = 0

-- count reductions using two different strategies
countReds :: LamExpr -> Int -> (Maybe Int, Maybe Int)
countReds e limit | (l <= limit) && (r <= limit) = (Just l, Just r)
                  | l <= limit = (Just l, Nothing)
                  | r <= limit = (Nothing, Just r)
                  | otherwise = (Nothing, Nothing)
                            where l = countLeft e
                                  r = countRight e

-- Challenge 5

-- data types for the arithmetic expressions
data AritmeticExpr = VAE Value | SAE Section deriving (Show, Eq)
data Section = S Value deriving (Show, Eq)
data Value = V1 Section Value | V2 Int | V3 Value Value deriving (Show,Eq)

-- definition of a value of type (Section Value)
val1 :: Parser Value
val1 = do x <- section
          y <- val
          return (V1 x y)

-- definition of a value of type (Natural)
val2 :: Parser Value
val2 = do x <- natural
          return (V2 x)

-- definition of a value of type (Value + Value)
val3 :: Parser Value
val3 = do x <- lowerVal
          symbol "+"
          y <- val
          return (V3 x y)

-- definition of the expressions of type value entry points
val :: Parser Value
val = val3 <|> lowerVal
lowerVal = val1 <|> val2

-- definition of a Section
section :: Parser Section
section = do  symbol "("
              symbol "+"
              v <- val
              symbol ")"
              return (S v)

-- definition of the value arithmetic expression
arithmeticVal :: Parser AritmeticExpr
arithmeticVal = do  v <- val
                    return (VAE v)

-- definition of the section arithmetic expression
arithmeticSec :: Parser AritmeticExpr
arithmeticSec = do  s <- section
                    return (SAE s)

-- definition of the entry points
arithm :: Parser AritmeticExpr
arithm = arithmeticVal <|> arithmeticSec

-- this function creates a LamApp between (LamVar 1) and a given LamExpr
fct :: LamExpr -> LamExpr
fct x = LamApp (LamVar 1) x

-- this function calls the fct function n times
rptFct :: Int -> LamExpr -> LamExpr
rptFct 0 x = x
rptFct n x = fct (rptFct (n-1) x)

-- this function creates the Church Numeral n
rpt :: Int -> LamExpr
rpt n = LamAbs 1 (LamAbs 2 (rptFct n (LamVar 2)))

-- this function creates the successor for a given n
-- function adapted from https://en.wikipedia.org/wiki/Church_encoding
successor :: Int -> LamExpr -> LamExpr
successor n x = LamApp x (LamApp (rptFct n x) (LamVar 3))

scc :: Int -> LamExpr -> LamExpr
scc n x = LamAbs 1 (LamAbs 2 (LamAbs 3 (successor n x)))

-- this function translates an arithmetic expression into a lambda expression
compileArithExpr :: AritmeticExpr -> LamExpr
compileArithExpr x = case x of
                          (VAE (V2 n)) ->  rpt n
                          (SAE (S (V2 n))) -> LamApp (rpt n) (scc n (LamVar 2))
                          (SAE (S x)) -> scc 1 (compileArithExpr (VAE x))
                          (VAE (V3 x y)) -> LamApp (compileArithExpr (VAE y)) (scc 1 (compileArithExpr (VAE x)))
                          (VAE (V1 s v )) -> LamApp (compileArithExpr (VAE v)) (compileArithExpr (SAE s))

-- compile an arithmetic expression into a lambda calculus equivalent
compileArith :: String -> Maybe LamExpr
compileArith s  | e == [] = Nothing
                | snd (head e) /= "" = Nothing
                | otherwise = Just (compileArithExpr (fst (head e)))
                          where e = parse arithm s


-- Tests

-- this part is adapted from the Test Harness file provided
tests :: [(String, [(String, Bool)])]
tests =
  [
  ("Challenge 1",
    [ ("Test 1",
        convertLet testExpr1 == LamApp (LamAbs 1 (LamApp (LamVar 2) (LamApp (LamVar 3) (LamVar 4)))) (LamAbs 2 (LamAbs 3 (LamAbs 4 (LamApp (LamVar 1) (LamVar 2)))))
      ),
      ("Test 2",
        convertLet testExpr2 == LamApp (LamVar 1) (LamApp (LamApp (LamAbs 1 (LamVar 2)) (LamVar 1)) (LamVar 3))
      ),
      ("Test 3",
        convertLet testExpr3 == LamApp (LamVar 2) (LamApp (LamVar 3) (LamVar 4))
      ),
      ("Test 4",
        convertLet testExpr4 ==  LamApp (LamAbs 1 (LamApp (LamVar 1) (LamApp (LamApp (LamAbs 1 (LamVar 2)) (LamVar 1)) (LamVar 3)))) (LamApp (LamAbs 1 (LamApp (LamVar 2) (LamApp (LamVar 3) (LamVar 4)))) (LamAbs 2 (LamAbs 3 (LamAbs 4 (LamApp (LamVar 1) (LamVar 2))))))
      )
    ]
  ),
  ("Challenge 2",
    [ ("Test 1",
        prettyPrint testExpr1 == "let x1 x2 x3 x4 = x1 x2 in x2 (x3 x4)"
      ),
      ("Test 2",
        prettyPrint testExpr4 == "let x1 = let x1 x2 x3 x4 = x1 x2 in x2 (x3 x4) in x1 ((let x1 = x1 in x2) x3)"
      ),
      ("Test 3",
        prettyPrint testExpr5 == "x1 (x2 (x3 x4 (x5 x6)) x7)"
      ),
      ("Test 4",
        prettyPrint testExpr2 == "x1 ((let x1 = x1 in x2) x3)"
      )
    ]
  ),
  ("Challenge 3",
    [ ("Test 1",
        parseLet "x1 in x2" == Nothing
      ),
      ("Test 2",
        parseLet "(x1 ((let x1 = x1 in x2) x3))" == Just testExpr6
      ),
      ("Test 3",
        (parseLet "letx1x2=x2inx1x1") == Just (Let [1,2] (Var 2) (App (Var 1) (Var 1)))
      ),
      ("Test 4",
        parseLet "x1 ((let x1 = x1 in x2) x3)" == Just testExpr2
      ),
      ("Test 5",
        parseLet "(x1 x2 x3 (x4) ()" == Nothing
      )
    ]
  ),
  ("Challenge 4",
    [ ("Test 1",
        countReds testLamExpr1 1 == (Nothing, Nothing)
      ),
      ("Test 2",
        countReds testLamExpr1 2 == (Just 2, Nothing)
      ),
      ("Test 3",
        countReds testLamExpr1 4 == (Just 2, Just 3)
      ),
      ("Test 4",
        countReds testLamExpr2 2 == (Just 1, Just 1)
      )
    ]
  ),
  ("Challenge 5",
    [ ("Test 1",
        compileArith "(0)" == Nothing
      ),
      ("Test 2",
       (compileArith "(+(+3))") == Nothing
      ),
      ("Test 3",
       (compileArith "(+2)") == Just (LamApp (LamAbs 1 (LamAbs 2 (LamApp (LamVar 1) (LamApp (LamVar 1) (LamVar 2))))) (LamAbs 1 (LamAbs 2 (LamAbs 3 (LamApp (LamVar 2) (LamApp (LamApp (LamVar 1) (LamApp (LamVar 1) (LamVar 2))) (LamVar 3)))))))
      )
    ]
  )
  ]

test :: IO ()
test =
  do
    putStr ""
    testSuite tests

testSuite :: [(String, [(String,Bool)])] -> IO ()
testSuite [] = putStr ""
testSuite ((s,tc):ts) =
  do
    putStrLn (outPrefix (s ++ ": " ++ (message tc)))
    testCases tc
    testSuite ts

testCases :: [(String,Bool)] -> IO ()
testCases [] = putStr ""
testCases ((s,False):ts) =
  do
    putStr (outPrefix "Failed: ")
    putStrLn s
    testCases ts
testCases ((s,True):ts) =
  do
    testCases ts

outPrefix msg = "  " ++ msg

message :: [(String,Bool)] -> String
message ts =
  let failures = [(s,b) | (s,b) <- ts , b == False] in
  if failures == [] then "all test cases passed"
  else "failed " ++ (show (length failures)) ++ " out of " ++ (show (length ts)) ++ " test cases"

-- constants for tests
testExpr1 = Let [1,2,3,4] (App (Var 1) (Var 2)) (App (Var 2) (App (Var 3) (Var 4)))
testExpr2 = App (Var 1) (App (Let [1] (Var 1) (Var 2)) (Var 3))
testExpr3 = App (Var 2) (App (Var 3) (Var 4))
testExpr4 = Let [1] testExpr1 testExpr2
testExpr5 = App (Var 1) (App (App (Var 2) (App (App (Var 3) (Var 4)) (App (Var 5) (Var 6)))) (Var 7))
testExpr6 = App (Var 1) (App (Let [1] (Var 1) (Var 2)) (Var 3))

testLamExpr1 = LamAbs 1 (LamApp (LamApp (LamVar 1) (LamVar 2)) (LamAbs 2 (LamApp (LamVar 4) (LamVar 3))))
testLamExpr2 = LamAbs 1 (LamAbs 2 (LamAbs 3 (LamApp (LamVar 1) (LamVar 2))))
