module TypedLambdaCalcInitial.Interpreters where
--module TypedLambdaCalcInitial.Interpreters (pretty, depth, size, multiStepEval, bigStepEval) where

import Control.Monad.Reader
import Data.List

import TypedLambdaCalcInitial.Types 

{-
----------------------
--- Pretty Printer ---
----------------------

primeSieve :: [Integer]
primeSieve = 2 : [i | i <- [3..], and [rem i p > 0 | p <- takeWhile (\p -> p^2 <= i) primeSieve]]

appendPrime :: String -> Int -> String
appendPrime str i = str ++ show (primeSieve !! i)

pickFreshName :: Context -> String -> (Context, String)
pickFreshName ctx str = f ctx str 0
  where f :: Context -> String -> Int -> (Context, String)
        f ctx' str' i = let res = find (== str') ctx'
                        in case res of
                             Nothing -> (str':ctx', str')
                             Just _  -> let str'' = appendPrime str i
                                        in f ctx' str'' (i+1)

pretty :: Term -> String
pretty t = runReader (f t) []
  where
    f :: Term -> Reader Context String
    f (App t1 t2) = do
      t1' <- f t1
      t2' <- f t2
      return $ "(" ++ t1' ++ " " ++ t2' ++ ")"
    f (Var x) = ask >>= \ctx -> return (ctx !! x)
    f (Abs x  t1) = do
      ctx <- ask
      let (ctx', x') = pickFreshName ctx x
      t1' <- local (const ctx') (f t1)
      return $ "(lambda " ++ x' ++ ". " ++ t1' ++ ")"


-------------
--- Depth ---
-------------

-- TOD0:
depth :: Term -> Integer
depth (Var _) = 0
depth (Abs _ t1) = 1 + depth t1
depth (App t1 t2) = depth t1 + depth t2


------------
--- Size ---
------------

-- TODO:
size :: Term -> Integer
size = undefined
-}
------------------
--- Evaluation ---
------------------

shift :: DeBruijn -> Term -> Term
shift target t = f 0 t
  where
    f :: Int -> Term -> Term
    f i (Var x) = if x >= i then Var (x + target) else Var x
    f i (Abs v ty t1) = Abs v ty $ f (i + 1) t1
    f i (App t1 t2) = App (f i t1) (f i t2)
    f i Tru = Tru
    f i Fls = Fls

{-
Substitution Rules:
1. [j -> s]k       = if j == k then s else k
2. [j -> s](\.t1)  = \.[j+1 -> ↑¹(s)]t1
2. [j -> s](t1 t2) = ([j -> s]t1 [j -> s]t2)

[1 -> 2]0 = 0
[1 -> 2]1 = 2
[1 -> 2]\.0 = \.0
[1 -> 2]\.1 = \.2
-}

subst :: DeBruijn -> Term -> Term -> Term
subst j s t = f 0 s t
  where f :: DeBruijn -> Term -> Term -> Term
        f c s' (Var x) = if x == j + c then s' else Var x
        f c s' (Abs v ty t) = Abs v ty (f (c+1) (shift c s') t)
        f c s' (App t1 t2) = App (f c s' t1) (f c s' t2)

substTop :: Term -> Term -> Term
substTop s t = shift (-1) (subst 0 (shift 1 s) t)

isVal :: Context -> Term -> Bool
isVal _ (Abs _ _ _) = True
isVal _ Tru = True
isVal _ Fls = True
isVal _ _ = False


-- Single Step Evaluation Function
singleEval :: Context -> Term -> Maybe Term
singleEval ctx t =
  case t of
    (App (Abs x _ t12) v2) | isVal ctx v2 -> return $ substTop v2 t12
    (App v1@(Abs _ _ _) t2) -> App v1 <$> singleEval ctx t2
    (App t1 t2) -> flip App t2 <$> singleEval ctx t1
    _ -> Nothing

-- Multistep Evaluation Function
multiStepEval :: Context -> Term -> Term
multiStepEval ctx t = maybe t (multiStepEval ctx) (singleEval ctx t)

-- Big Step Evaluation Function
bigStepEval :: Context -> Term -> Term
bigStepEval _ t@(Abs _ _ _) = t
bigStepEval ctx (App t1 t2) =
  let (Abs _ _ t12) = bigStepEval ctx t1
      v2  = bigStepEval ctx t2
  in bigStepEval ctx $ substTop v2 t12
bigStepEval _ Tru = Tru
bigStepEval _ Fls = Fls

exp0 :: Term
exp0 = Tru

ctx0 :: Context
ctx0 = []

exp1 :: Term
exp1 = Var 0

ctx1 :: Context
ctx1 = [("x", VarBind Boo)]

exp2 :: Term
exp2 = (Abs "x" Boo (Var 0))

ctx2 :: Context
ctx2 = []

exp3 :: Term
exp3 = (Abs "x" Boo (Abs "p" Boo (Var 0)))

exp4 :: Term
exp4 = (App (App (Abs "x" Boo (Abs "p" Boo (Var 0))) Tru) Fls)
