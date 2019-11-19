module TypedLambdaCalcInitial.Interpreters where

import Control.Applicative
import Data.Monoid (Sum(..))
import Data.List (find)

import TypedLambdaCalcInitial.Types


-------------
--- Depth ---
-------------

depth :: Term -> Integer
depth (Var _) = 0
depth (Abs _ _ t1) = 1 + depth t1
depth (App t1 t2) = depth t1 + depth t2
depth Tru = 0
depth Fls = 0
depth Z = 0
depth Unit = 0
depth (As t1 _) = depth t1
depth (S t) = depth t
depth (If t1 t2 t3) = depth t1 + depth t2 + depth t3
depth (Case l m _ n) = depth l + depth m + depth n
depth (Let _ t1 t2) = 1 + depth t1 + depth t2
depth (Pair t1 t2) = depth t1 + depth t2
depth (Fst t1) = depth t1
depth (Snd t1) = depth t1
depth (Tuple ts) = getSum $ foldMap (Sum . depth . snd) ts
depth (Record ts) = getSum $ foldMap (Sum . depth . snd) ts
depth (Get t1 _) = 1 + depth t1


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
    f i (InL t1 ty) = InL (f i t1) ty
    f i (InR t1 ty) = InR (f i t1) ty
    f i (SumCase t1 tL vL tR vR) = SumCase (f i t1) (f (i + 1) tL) vL (f (i + 1) tR) vR
    f i (Tag tag t1 ty) = Tag tag (f i t1) ty
    f i (VariantCase t1 cases) = VariantCase (f i t1) $ cases >>= \(tag, bnd, trm) -> pure (tag, bnd, f (i + 1) trm)
    f i (Fix t1) = Fix (f i t1)

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
        f c s' (InL t1 ty) = InL (f c s' t1) ty
        f c s' (InR t1 ty) = InR (f c s' t1) ty
        f c s' (SumCase t1 tL vL tR vR) =
          SumCase (f c s' t1)
                  (f (c + 1) (shift c s') tL)
                  vL
                  (f (c + 1) (shift c s') tR)
                  vR
        f c s' (Tag tag t1 ty) = Tag tag (f c s' t1) ty
        f c s' (VariantCase t1 cases) = let cases' = ((fmap . fmap) (f (c + 1) (shift c s')) cases)
                                        in VariantCase (f c s' t1) cases'
        f c s' (Fix t1) = Fix (f c s' t1)

substTop :: Term -> Term -> Term
substTop s t = shift (-1) (subst 0 (shift 1 s) t)

-- TODO: Reimplement with `Data Term' a = Reduced a | Unreduced a`
-- TODO: Be more consistent with `not isVal` vs `isVal`. Will casing on `Term'` make this irrelevent? Yes?
-- Single Step Evaluation Function
singleEval :: Context -> Term -> Maybe Term
singleEval ctx t =
  case t of
    (App (Abs _ _ t12) v2) | isVal ctx v2 -> pure $ substTop v2 t12
    (App v1@(Abs _ _ _) t2)               -> App v1 <$> singleEval ctx t2
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
          evalElem ((v, t1):ts') = let t1' = (,) v <$> (singleEval ctx t1) in liftA2 (:) t1' (pure ts')
      in Tuple <$> evalElem ts
    (Record ts) -> do
      let evalElem [] = Nothing
          evalElem ((v, t1):ts') | isVal ctx t1 = let ts'' = evalElem ts' in ((:) (v, t1)) <$> ts''
          evalElem ((v, t1):ts') = let t1' = (,) v <$> (singleEval ctx t1) in liftA2 (:) t1' (pure ts')
      Record <$> evalElem ts
    (Get (Tuple ts) var) -> lookup var ts
    (Get (Record ts) var) -> lookup var ts
    (Get t1 var) | not $ isVal ctx t1 -> singleEval ctx t1 >>= \t1' -> pure (Get t1' var)
    (SumCase t1 tL vL tR vR) | not $ isVal ctx t1 ->
      singleEval ctx t1 >>= \t1' -> pure (SumCase t1' tL vL tR vR)
    (SumCase (InL t1 _) tL _ _ _) -> pure $ substTop t1 tL
    (SumCase (InR t1 _) _ _ tR _) -> pure $ substTop t1 tR
    (InL t1 ty) -> flip InR ty <$> singleEval ctx t1
    (InR t1 ty) -> flip InR ty <$> singleEval ctx t1
    (Tag tag t1 ty) -> singleEval ctx t1 >>= \t1' -> pure $ Tag tag t1' ty
    (VariantCase t1 cases) | not $ isVal ctx t1 -> singleEval ctx t1 >>= \t1' -> pure (VariantCase t1' cases)
    (VariantCase t1 cases) ->
      case t1 of
        (Tag tag t1' _) -> case find (\(tag',_,_) -> tag == tag') cases of
          Just (_,_, term) -> pure $ substTop t1' term
          Nothing -> Nothing
        _ -> Nothing
    (Fix t1) | not (isVal ctx t1) -> singleEval ctx t1 >>= pure . Fix
    (Fix (Abs _ _ t2)) -> pure $ substTop t t2
    (Roll ty t1) | not $ isVal ctx t1 -> singleEval ctx t1 >>= pure . (Roll ty)
    (Unroll ty t1) | not $ isVal ctx t1 -> singleEval ctx t1 >>= pure . (Unroll ty)
    (Unroll _ (Roll _ t1)) -> singleEval ctx t1 -- NOTE: Suspect?
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
bigStepEval ctx (SumCase t1 tL _ tR _) =
   let t1' = bigStepEval ctx t1
   in case t1' of
     (InL t1'' _) -> bigStepEval ctx $ substTop t1'' tL
     (InR t1'' _) -> bigStepEval ctx $ substTop t1'' tR
     x -> error $ show x -- NOTE: Typechecker should make this state impossible
bigStepEval ctx (VariantCase t1 cases) =
  let t1' = bigStepEval ctx t1
  in undefined
bigStepEval _ t@(InL _ _) = t
bigStepEval _ t@(InR _ _) = t
bigStepEval _ t@(Tag _ _ _) = t
bigStepEval _ Unit = Unit
bigStepEval _ Tru = Tru
bigStepEval _ Fls = Fls
bigStepEval _ Z = Z
bigStepEval ctx (S t1) = S $ bigStepEval ctx t1
bigStepEval _ x = error $ show x
