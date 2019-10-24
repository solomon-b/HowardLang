module TypedLambdaCalcInitial.Interpreters where
--module TypedLambdaCalcInitial.Interpreters (pretty, depth, size, multiStepEval, bigStepEval) where

import Control.Monad.Reader

import Data.List

import TypedLambdaCalcInitial.Types


----------------------
--- Pretty Printer ---
----------------------

primeSieve :: [Integer]
primeSieve = 2 : [i | i <- [3..], and [rem i p > 0 | p <- takeWhile (\p -> p^(2 :: Integer) <= i) primeSieve]]

appendPrime :: String -> Int -> String
appendPrime str i = str ++ show (primeSieve !! i)

pickFreshName :: Bindings -> String -> (Bindings, String)
pickFreshName ctx str = f ctx str 0
  where f :: Bindings -> String -> Int -> (Bindings, String)
        f ctx' str' i = let res = find (== str') ctx'
                        in case res of
                             Nothing -> (Snoc ctx' str', str')
                             Just _  -> let str'' = appendPrime str i
                                        in f ctx' str'' (i+1)

showNat :: Term -> String
showNat nat = show $ f nat
  where
    f :: Term -> Int
    f Z = 0
    f (S n) = 1 + f n
    f _ = undefined

pretty :: Term -> String
pretty t = runReader (f t) Nil
  where
    f :: Term -> Reader Bindings String
    f (App t1 t2) = do
      t1' <- f t1
      t2' <- f t2
      return $ "(" ++ t1' ++ " " ++ t2' ++ ")"
    f (Var x) = ask >>= \ctx -> return $ ctx !!! x
    f (Abs x _ t1) = do
      ctx <- ask
      let (ctx', x') = pickFreshName ctx x
      t1' <- local (const ctx') (f t1)
      return $ "(lambda " ++ x' ++ ". " ++ t1' ++ ")"
    f Tru = return "True"
    f Fls = return "False"
    f Z = return "0"
    f s@(S _) = return $ showNat s
    f (If t1 t2 t3) = do
      t1' <- f t1
      t2' <- f t2
      t3' <- f t3
      return $ "If " ++ t1' ++ " then " ++ t2' ++ " else " ++ t3'


-------------
--- Depth ---
-------------

-- TOD0:
depth :: Term -> Integer
depth (Var _) = 0
depth (Abs _ _ t1) = 1 + depth t1
depth (App t1 t2) = depth t1 + depth t2
depth Tru = 0
depth Fls = 0
depth Z = 0
depth (S t) = depth t
depth (If t1 t2 t3) = depth t1 + depth t2 + depth t3


------------
--- Size ---
------------

-- TODO:
size :: Term -> Integer
size = undefined


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
    f _ Tru = Tru
    f _ Fls = Fls
    f _ Z = Z
    f i (S t1) = S (f i t1)
    f i (If t1 t2 t3) = If (f i t1) (f i t2) (f i t3)

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
        f c s' (Abs v ty _) = Abs v ty (f (c+1) (shift c s') t)
        f c s' (App t1 t2) = App (f c s' t1) (f c s' t2)
        f _ _ Tru = Tru
        f _ _ Fls = Fls
        f c s' (If t1 t2 t3) = If (f c s' t1) (f c s' t2) (f c s' t3)
        f _ _ Z = Z
        f c s' (S t1) = S (f c s' t1)

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
    (App (Abs _ _ t12) v2) | isVal ctx v2 -> return $ substTop v2 t12
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
bigStepEval _ x = error $ show x
