module HowardLang.Interpreters where

import Control.Monad.Reader
import Control.Applicative
import Data.Functor.Foldable
import Data.List (find)
import Lens.Micro

import HowardLang.Types
import HowardLang.Typechecker


--------------------------
--- Tree Manipulations ---
--------------------------

ascribeRolls :: Term -> Term
ascribeRolls = cata algebra
  where
    algebra = \case
      RollF u@(FixT _ ty) t1 ->
        let u'  = typeSubstTop u ty
            t1' = cata (embed . ascribeChildRollsF u) t1
        in cata (embed . ascribeTagsF u') t1'
      t1 -> embed t1

ascribeChildRollsF :: Type -> TermF Term -> TermF Term
ascribeChildRollsF fixT = \case
  TagF v t1 -> RollF fixT (Tag v t1)
  t1 -> t1

ascribeTagsF :: Type -> TermF Term -> TermF Term
ascribeTagsF as = \case
  TagF v t1 -> AsF (Tag v t1) as
  t1 -> t1

stripAscriptions :: Term -> Term
stripAscriptions = cata algebra
  where
    algebra = \case
      AsF t1 _ -> t1
      t1       -> embed t1

depth :: Term -> Integer
depth = cata algebra
  where
    algebra = \case
      VarF _ -> 0
      UnitF  -> 0
      TruF   -> 0
      FlsF   -> 0
      ZF     -> 0
      t      -> maximum $ fmap (+1) t

size :: Term -> Integer
size = cata $ foldr (+) 1

------------------
--- Evaluation ---
------------------

{-
TODO: Update Substition Rules for all new terms
Substitution Rules:
1. [j -> s]k       = if j == k then s else k
2. [j -> s](\.t1)  = \.[j+1 -> ↑¹(s)]t1
2. [j -> s](t1 t2) = ([j -> s]t1 [j -> s]t2)

[1 -> 2]0 = 0
[1 -> 2]1 = 2
[1 -> 2]\.0 = \.0
[1 -> 2]\.1 = \.2
-}

mkTermAlg :: (Int -> Reader ctx Term) -> (ctx -> ctx) -> (TermF (Reader ctx Term) -> Reader ctx Term)
mkTermAlg baseCase update = \case
  VarF x                -> baseCase x
  AbsF v ty t1          -> Abs v ty <$> local update t1
  LetF v t1 t2          -> t1 >>= \t1' -> Let v t1' <$> local update t2
  CaseF l m x n         -> l >>= \l' -> m >>= \m' -> Case l' m' x <$> local update n
  VariantCaseF t1 cases -> do
    t1' <- t1
    cases' <- (traverse . traverseOf _3) (local update) cases
    pure $ VariantCase t1' cases'
  t -> fmap embed (sequenceA t)

shift :: DeBruijn -> Term -> Term
shift target t = runReader (cataA algebra t) 0
  where
    algebra :: TermF (Reader Int Term) -> Reader Int Term
    algebra = mkTermAlg baseCase update
    update :: Int -> Int
    update = (+1)
    baseCase :: Int -> Reader Int Term
    baseCase x = ask >>= \i -> if x >= i then pure (Var (x + target)) else pure (Var x)

subst :: DeBruijn -> Term -> Term -> Term
subst target s t = runReader (cataA algebra t) (s, 0)
  where
    algebra :: TermF (Reader (Term, Int) Term) -> Reader (Term, Int) Term
    algebra = mkTermAlg baseCase update
    update :: (Term, Int) -> (Term, Int)
    update (s', c) = (shift c s', c+1)
    baseCase :: Int -> Reader (Term, Int) Term
    baseCase x = ask >>= \ctx -> if x == target + snd ctx then pure (fst ctx) else pure (Var x)

substTop :: Term -> Term -> Term
substTop s t = shift (-1) (subst 0 (shift 1 s) t)

------------------
--- Evaluators ---
------------------
-- TODO: Reimplement with `Data Term' a = Reduced a | Unreduced a`
-- TODO: Be more consistent with `not isVal` vs `isVal`. Will casing on `Term'` make this irrelevent? Yes?

singleEval :: Context -> Term -> Maybe Term
singleEval ctx t =
  case t of
    (App (Abs _ _ t12) v2) | isVal ctx v2 -> pure $ substTop v2 t12
    (App v1@Abs{} t2)               -> App v1 <$> singleEval ctx t2
    (App t1 t2)                           -> singleEval ctx t1 >>= \t1' -> pure $ App t1' t2
    (If Tru t2 _)                         -> pure t2
    (If Fls _ t3)                         -> pure t3
    (If t1 t2 t3)                         -> singleEval ctx t1 >>= \t1' -> pure $ If t1' t2 t3
    (S n) | not $ isVal ctx n             -> S <$> singleEval ctx n
    (Case Z m _ _)                        -> pure m
    (Case (S l) _ _ n) | isVal ctx l      -> pure $ substTop l n
    (Case l m x n)                        -> singleEval ctx l >>= \l' -> pure $ Case l' m x n
    (As t1 _)                             -> pure t1
    (Let _ v1 t2) | isVal ctx v1          -> pure $ substTop v1 t2
    (Let v t1 t2)                         -> singleEval ctx t1 >>= \t1' -> pure $ Let v t1' t2
    (Fst (Pair t1 _))                     -> pure t1
    (Fst t1)                              -> singleEval ctx t1 >>= \t1' -> pure $ Fst t1'
    (Snd (Pair _ t2))                     -> pure t2
    (Snd t1)                              -> singleEval ctx t1 >>= \t1' -> pure $ Snd t1'
    (Pair t1 t2) | not $ isVal ctx t1     -> singleEval ctx t1 >>= \v1 -> pure $ Pair v1 t2
    (Pair t1 t2)                          -> singleEval ctx t2 >>= \v2 -> pure $ Pair t1 v2
    (Tuple ts) ->
      let evalElem [] = Nothing
          evalElem ((v, t1):ts') | isVal ctx t1 = let ts'' = evalElem ts' in ((:) (v, t1)) <$> ts''
          evalElem ((v, t1):ts') = let t1' = (,) v <$> singleEval ctx t1 in liftA2 (:) t1' (pure ts')
      in Tuple <$> evalElem ts
    (Record ts) -> do
      let evalElem [] = Nothing
          evalElem ((v, t1):ts') | isVal ctx t1 = let ts'' = evalElem ts' in ((:) (v, t1)) <$> ts''
          evalElem ((v, t1):ts') = let t1' = (,) v <$> singleEval ctx t1 in liftA2 (:) t1' (pure ts')
      Record <$> evalElem ts
    (Get (Tuple ts) var) -> lookup var ts
    (Get (Record ts) var) -> lookup var ts
    (Get t1 var) | not $ isVal ctx t1 -> singleEval ctx t1 >>= \t1' -> pure (Get t1' var)
    (Tag tag t1) -> singleEval ctx t1 >>= \t1' -> pure $ Tag tag t1'
    (VariantCase t1 cases) | not $ isVal ctx t1 -> singleEval ctx t1 >>= \t1' -> pure (VariantCase t1' cases)
    (VariantCase t1 cases) ->
      case t1 of
        (Tag tag t1') -> case find (\(tag',_,_) -> tag == tag') cases of
          Just (_,_, term) -> pure $ substTop t1' term
          Nothing -> Nothing
        _ -> Nothing
    (FixLet t1) | not (isVal ctx t1) -> singleEval ctx t1 >>= pure . FixLet
    (FixLet (Abs _ _ t2)) -> pure $ substTop t t2
    (Roll ty t1) | not $ isVal ctx t1 -> singleEval ctx t1 >>= pure . (Roll ty)
    (Unroll ty t1) | not $ isVal ctx t1 -> singleEval ctx t1 >>= pure . (Unroll ty)
    (Unroll _ (Roll _ v1)) | isVal ctx v1 -> pure v1
    _ -> Nothing

-- Multistep Evaluation Function
multiStepEval :: Context -> Term -> Term
multiStepEval ctx t = let t' = stripAscriptions t in maybe t' (multiStepEval ctx) (singleEval ctx t')

-- Big Step Evaluation Function
bigStepEval :: Context -> Term -> Term
bigStepEval _ t@Abs{} = t
bigStepEval ctx (App t1 t2) =
  let (Abs _ _ t12) = bigStepEval ctx t1
      v2  = bigStepEval ctx t2
  in bigStepEval ctx $ substTop v2 t12
bigStepEval ctx (If t1' t2' t3') =
  case bigStepEval ctx t1' of
    Tru -> bigStepEval ctx t2'
    Fls -> bigStepEval ctx t3'
    x   -> error $ show x -- NOTE: Typechecker should make this state impossible
bigStepEval ctx (Case l m _ n) =
  case bigStepEval ctx l of
    Z -> bigStepEval ctx m
    (S l') -> bigStepEval ctx $ substTop l' n
    x -> error $ show x -- NOTE: Typechecker should make this state impossible
bigStepEval ctx (As t1 _) = bigStepEval ctx t1
bigStepEval ctx (Let _ t1 t2) =
  let t1' = bigStepEval ctx t1
  in bigStepEval ctx $ substTop t1' t2
bigStepEval _ (Fst (Pair t1 _)) = t1
bigStepEval ctx (Fst t1) = bigStepEval ctx t1
bigStepEval _ (Snd (Pair _ t2)) = t2
bigStepEval ctx (Snd t1) = bigStepEval ctx t1
bigStepEval ctx (Pair t1 t2) = Pair (bigStepEval ctx t1) (bigStepEval ctx t2)
bigStepEval ctx (Tuple ts) = Tuple $ ts >>= \(v,t) -> pure (v, bigStepEval ctx t)
bigStepEval ctx (Record ts) = Record $ ts >>= \(v,t) -> pure (v, bigStepEval ctx t)
bigStepEval ctx (VariantCase t1 cases) =
  let t1' = bigStepEval ctx t1
  in undefined -- TODO: Implement bigstep variantcase eval
bigStepEval _ t@(Tag _ _) = t
bigStepEval ctx t@(FixLet t1) = bigStepEval ctx $ substTop t t1
bigStepEval ctx (Roll ty t1) = Roll ty $ bigStepEval ctx t1
bigStepEval ctx (Unroll _ (Roll _ t1)) = bigStepEval ctx t1
bigStepEval ctx (Unroll ty t1) = Unroll ty $ bigStepEval ctx t1
bigStepEval _ Unit = Unit
bigStepEval _ Tru = Tru
bigStepEval _ Fls = Fls
bigStepEval _ Z = Z
bigStepEval ctx (S t1) = S $ bigStepEval ctx t1
bigStepEval _ x = error $ show x
