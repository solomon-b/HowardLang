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

addPrevious :: [Int] -> [Int]
addPrevious xs = runReader (cataA algebra xs) 0
  where
    algebra :: ListF Int (Reader Int [Int]) -> Reader Int [Int]
    algebra Nil = pure []
    algebra (Cons curr rest) = do
      prev <- ask
      pure $ (curr + prev) : runReader rest curr

shiftF :: DeBruijn -> Term -> Term
shiftF target t = runReader (cataA algebra t) target
  where
    algebra :: TermF (Reader Int Term) -> Reader Int Term
    algebra = \case
      VarF x -> ask >>= \i -> if x >= i then pure (Var (x + target)) else pure (Var x)
      AbsF v ty t1 -> Abs v ty <$> local (+1) t1
      LetF v t1 t2 -> t1 >>= \t1' -> Let v t1' <$> local (+1) t2
      CaseF l m x n -> l >>= \l' -> m >>= \m' -> Case l' m' x <$> local (+1) n
      VariantCaseF t1 cases -> do
        t1' <- t1
        cases' <- (traverse . traverseOf _3) (local (+1)) cases
        pure $ VariantCase t1' cases'
      TruF -> pure Tru
      FlsF -> pure Fls
      UnitF -> pure Unit
      ZF -> pure Z
      SF t1 -> S <$> t1
      AppF t1 t2 -> App <$> t1 <*> t2
      IfF t1 t2 t3 -> t1 >>= \t1' -> t2 >>= \t2' -> t3 >>= \t3' -> pure $ If t1' t2' t3'
      AsF t1 ty -> flip As ty <$> t1
      PairF t1 t2 -> Pair <$> t1 <*> t2
      FstF t1 -> Fst <$> t1
      SndF t1 -> Snd <$> t1
      TupleF ts -> Tuple <$> (traverse . traverse) id ts
      RecordF ts -> Record <$> (traverse . traverse) id ts
      GetF t1 v -> flip Get v <$> t1
      TagF tag t1 -> Tag tag <$> t1
      FixLetF t1 -> FixLet <$> t1
      RollF ty t1 -> Roll ty <$> t1
      UnrollF ty t1 -> Unroll ty <$> t1

shift :: DeBruijn -> Term -> Term
shift target t = f 0 t
  where
    f :: Int -> Term -> Term
    f i (Var x) = if x >= i then Var (x + target) else Var x
    f i (Abs v ty t1) = Abs v ty $ f (i + 1) t1
    f i (App t1 t2) = App (f i t1) (f i t2)
    f _ Tru = Tru
    f _ Fls = Fls
    f _ Unit = Unit
    f _ Z = Z
    f i (S t1) = S (f i t1)
    f i (If t1 t2 t3) = If (f i t1) (f i t2) (f i t3)
    f i (Case l m x n) = Case (f i l) (f i m) x (f (i + 1) n)
    f i (As t1 ty) = As (f i t1) ty
    f i (Let v t1 t2) = Let v (f i t1) (f (i + 1) t2)
    f i (Pair t1 t2) = Pair (f i t1) (f i t2)
    f i (Fst t1) = Fst (f i t1)
    f i (Snd t1) = Snd (f i t1)
    f i (Tuple ts) = Tuple $ (fmap . fmap) (f i) ts
    f i (Record ts) = Record $ (fmap . fmap) (f i) ts
    f i (Get t1 v) = Get (f i t1) v
    f i (Tag tag t1) = Tag tag (f i t1)
    f i (VariantCase t1 cases) = VariantCase (f i t1) $ cases >>= \(tag, bnd, trm) -> pure (tag, bnd, f (i + 1) trm)
    f i (FixLet t1) = FixLet (f i t1)
    f i (Roll ty t1) = Roll ty (f i t1)
    f i (Unroll ty t1) = Unroll ty (f i t1)

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

-- NOTE: Would lenses help clean up this sort of nonsense?
subst :: DeBruijn -> Term -> Term -> Term
subst j s t = f 0 s t
  where f :: DeBruijn -> Term -> Term -> Term
        f c s' (Var x) = if x == j + c then s' else Var x
        f c s' (Abs v ty t') = Abs v ty (f (c+1) (shift c s') t')
        f c s' (App t1 t2) = App (f c s' t1) (f c s' t2)
        f _ _ Tru = Tru
        f _ _ Fls = Fls
        f _ _ Unit = Unit
        f c s' (If t1 t2 t3) = If (f c s' t1) (f c s' t2) (f c s' t3)
        f _ _ Z = Z
        f c s' (S t1) = S (f c s' t1)
        f c s' (Case l m x n) =
          Case (f c s' l)
               (f c s' m)
               x
               (f (c+1) (shift c s') n)
        f c s' (As t1 ty) = As (f c s' t1) ty
        f c s' (Let v t1 t2) = Let v (f c s' t1) (f (c+1) (shift c s') t2)
        f c s' (Pair t1 t2) = Pair (f c s' t1) (f c s' t2)
        f c s' (Fst t1) = Fst (f c s' t1)
        f c s' (Snd t1) = Snd (f c s' t1)
        f c s' (Tuple ts) = Tuple $ (fmap . fmap) (f c s' ) ts
        f c s' (Record ts) = Record $ (fmap . fmap) (f c s' ) ts
        f c s' (Get t1 v) = Get (f c s' t1) v
        f c s' (Tag tag t1) = Tag tag (f c s' t1)
        f c s' (VariantCase t1 cases) = let cases' = ((fmap . fmap) (f (c + 1) (shift c s')) cases)
                                        in VariantCase (f c s' t1) cases'
        f c s' (FixLet t1) = FixLet (f c s' t1)
        f c s' (Roll ty t1) = Roll ty (f c s' t1)
        f c s' (Unroll ty t1) = Unroll ty (f c s' t1)

substTop :: Term -> Term -> Term
substTop s t = shift (-1) (subst 0 (shift 1 s) t)

-- TODO: Reimplement with `Data Term' a = Reduced a | Unreduced a`
-- TODO: Be more consistent with `not isVal` vs `isVal`. Will casing on `Term'` make this irrelevent? Yes?
-- Single Step Evaluation Function
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
