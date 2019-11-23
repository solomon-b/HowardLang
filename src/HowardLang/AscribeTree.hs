module HowardLang.AscribeTree where

import HowardLang.Types
import HowardLang.Typechecker

ascribeRolls :: Term -> Term
ascribeRolls = f
  where
    f (Tag v t1) = Tag v (f t1)
    f (Abs v ty t1) = Abs v ty (f t1)
    f (App t1 t2) = App (f t1) (f t2)
    f (If t1 t2 t3) = If (f t1) (f t2) (f t3)
    f (S t1) = S (f t1)
    f (Case t1 t2 v t3) = Case (f t1) (f t2) v (f t3)
    f (As t1 ty) = As (f t1) ty
    f (Let v t1 t2) = Let v (f t1) (f t2)
    f (Pair t1 t2) = Pair (f t1) (f t2)
    f (Fst t1) = Fst (f t1)
    f (Snd t1) = Snd (f t1)
    f (Tuple ts) = Tuple $ (fmap . fmap) f ts
    f (Get t1 v) = Get (f t1) v
    f (Record ts) = Record $ (fmap . fmap) f ts
    f (InL t1 ty) = InL (f t1) ty
    f (InR t1 ty) = InR (f t1) ty
    f (SumCase t1 t2 bndr t3 bndr') = SumCase (f t1) (f t2) bndr (f t3) bndr'
    f (VariantCase t1 ts) = VariantCase (f t1) $ (fmap . fmap) f ts
    f (Fix t1) = Fix (f t1)
    f (Roll u@(FixT _ ty) t1) =
      let u' = typeSubstTop u ty
          t1' = ascribeChildRolls u t1
      in ascribeTags u' t1'
    f (Unroll ty t1) = Unroll ty (f t1)
    f t1 = t1

ascribeChildRolls :: Type -> Term -> Term
ascribeChildRolls fixT = f
  where
    f (Abs v ty t1) = Abs v ty (f t1)
    f (App t1 t2) = App (f t1) (f t2)
    f (If t1 t2 t3) = If (f t1) (f t2) (f t3)
    f (S t1) = S (f t1)
    f (Case t1 t2 v t3) = Case (f t1) (f t2) v (f t3)
    f (As t1 ty) = As (f t1) ty
    f (Let v t1 t2) = Let v (f t1) (f t2)
    f (Pair t1 t2) = Pair (f t1) (f t2)
    f (Fst t1) = Fst (f t1)
    f (Snd t1) = Snd (f t1)
    f (Tuple ts) = Tuple $ (fmap . fmap) f ts
    f (Get t1 v) = Get (f t1) v
    f (Record ts) = Record $ (fmap . fmap) f ts
    f (InL t1 ty) = InL (f t1) ty
    f (InR t1 ty) = InR (f t1) ty
    f (SumCase t1 t2 bndr t3 bndr') = SumCase (f t1) (f t2) bndr (f t3) bndr'
    f (VariantCase t1 ts) = VariantCase (f t1) $ (fmap . fmap) f ts
    f (Fix t1) = Fix (f t1)
    f (Roll u@(FixT _ _) (Tag v t1)) = Roll u (Tag v (f t1))
    f (Roll u@(FixT _ _) t1) = Roll u (f t1)
    f (Unroll ty t1) = Unroll ty (f t1)
    f (Tag v t1) = Roll fixT (Tag v (f t1))
    f t1 = t1

ascribeTags :: Type -> Term -> Term
ascribeTags as = f
  where
    f (Tag v t1) = As (Tag v (f t1)) as
    f (Abs v ty t1) = Abs v ty (f t1)
    f (App t1 t2) = App (f t1) (f t2)
    f (If t1 t2 t3) = If (f t1) (f t2) (f t3)
    f (S t1) = S (f t1)
    f (Case t1 t2 v t3) = Case (f t1) (f t2) v (f t3)
    f (As t1 ty) = As (f t1) ty
    f (Let v t1 t2) = Let v (f t1) (f t2)
    f (Pair t1 t2) = Pair (f t1) (f t2)
    f (Fst t1) = Fst (f t1)
    f (Snd t1) = Snd (f t1)
    f (Tuple ts) = Tuple $ (fmap . fmap) f ts
    f (Get t1 v) = Get (f t1) v
    f (Record ts) = Record $ (fmap . fmap) f ts
    f (InL t1 ty) = InL (f t1) ty
    f (InR t1 ty) = InR (f t1) ty
    f (SumCase t1 t2 bndr t3 bndr') = SumCase (f t1) (f t2) bndr (f t3) bndr'
    f (VariantCase t1 ts) = VariantCase (f t1) $ (fmap . fmap) f ts
    f (Fix t1) = Fix (f t1)
    f (Roll ty t1) = Roll ty (f t1)
    f (Unroll ty t1) = Unroll ty (f t1)
    f t1 = t1


-----------------------------
--- Strip Out Ascriptions ---
-----------------------------

stripAscriptions :: Term -> Term
stripAscriptions t = f t
  where
    f = \case
      (As t1 _)                   -> f t1
      (Abs v ty t1)               -> Abs v ty (f t1)
      (App t1 t2)                 -> App (f t1) (f t2)
      (If t1 t2 t3)               -> If (f t1) (f t2) (f t3)
      (S t1)                      -> S (f t1)
      (Case t1 t2 v t3)           -> Case (f t1) (f t2) v (f t3)
      (Let v t1 t2)               -> Let v (f t1) (f t2)
      (Pair t1 t2)                -> Pair (f t1) (f t2)
      (Fst t1)                    -> Fst (f t1)
      (Snd t1)                    -> Snd (f t1)
      (Tuple ts)                  -> Tuple ((fmap . fmap) f ts)
      (Get t1 v)                  -> Get (f t1) v
      (Record ts)                 -> Record ((fmap . fmap) f ts)
      (InL t1 ty)                 -> InL (f t1) ty
      (InR t1 ty)                 -> InR (f t1) ty
      (SumCase t1 t2 bnd t3 bnd2) -> SumCase (f t1) (f t2) bnd (f t3) bnd2
      (Tag tag t1)                -> Tag tag (f t1)
      (VariantCase t1 ts)         -> VariantCase (f t1) ((fmap . fmap) f ts)
      (Fix t1)                    -> Fix (f t1)
      (Roll ty t1)                -> Roll ty (f t1)
      (Unroll ty t1)              -> Unroll ty (f t1)
      t'                          -> t'
