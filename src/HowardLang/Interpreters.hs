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
-- TODO: Eliminate need for `isVal`. I should be able to do this in all cases with clever use of `para` such
-- as the `AppF` case.

singleEval :: Term -> Maybe Term
singleEval = para ralgebra
  where
    ralgebra :: TermF (Term, Maybe Term) -> Maybe Term
    ralgebra = \case
      AppF (v1@(Abs _ _ term12), _) (term2, mstepped2) -> pure $ case mstepped2 of
        Just stepped2 -> App v1 stepped2 -- term2 reduced to stepped2
        Nothing -> substTop term2 term12 -- source2 is fully reduced
      AppF term1 term2 -> App <$> reduced term1 <*> source term2
      SF term -> S <$> reduced term
      IfF (Tru, _) term2 _ -> source term2
      IfF (Fls, _) _ term3 -> source term3
      IfF t1 t2 t3 -> If <$> reduced t1 <*> source t2 <*> source t3
      CaseF (Z, _) term2 _ _ -> pure $ viewTerm term2
      CaseF (S l, _) _ _ term3 | isVal l -> substTop l <$> source term3
      CaseF l m x n -> Case <$> reduced l <*> source m <*> pure x <*> source n
      AsF term1 _ -> reduced term1
      LetF ty term1 term2 -> case reduced term1 of
        Just stepped1 -> Let ty stepped1 <$> source term2
        Nothing -> substTop <$> source term1 <*> source term2
      FstF (Pair term1 _, _) -> pure term1
      FstF term -> source term
      SndF (Pair _ term2, _) -> pure term2
      SndF term -> source term
      PairF term1 term2 -> case reduced term1 of
        Just stepped1 -> Pair stepped1 <$> source term2
        Nothing -> Pair <$> source term1 <*> reduced term2
      TupleF ts | all (isVal . fst . snd) ts -> Nothing
      TupleF ts -> pure . Tuple $ (fmap . fmap) viewTerm ts
      RecordF ts | all (isVal . fst . snd) ts -> Nothing
      RecordF ts -> pure . Record $ (fmap . fmap) viewTerm ts
      GetF term var -> case fst term of
        Tuple ts -> lookup var ts
        Record ts -> lookup var ts
        steppedTerm | not $ isVal steppedTerm -> Get <$> reduced term <*> pure var
        _ -> error "Type Checker failed to catch unsound term"
      TagF tag term -> Tag tag <$> reduced term
      VariantCaseF t1 patterns | not $ isVal . fst $ t1 ->
        pure $ VariantCase (viewTerm t1) ((fmap . fmap) fst patterns)
      VariantCaseF t1 patterns ->
        case viewTerm t1 of
          Tag tag t1' -> case find (\(tag', _, _) -> tag == tag') patterns of
            Just (_,_, term) -> substTop t1' <$> source term
            Nothing -> Nothing
          _ -> Nothing
      FixLetF t1 | not . isVal . fst $ t1 -> reduced t1
      FixLetF (t@(Abs _ _ t2), _) -> pure $ substTop (FixLet t) t2
      RollF ty term | not . isVal . fst $ term -> Roll ty <$> reduced term
      UnrollF ty term | not . isVal . fst $ term -> Unroll ty <$> reduced term
      UnrollF _ (Roll _ v1, _) -> pure v1
      _ -> Nothing
    reduced = snd
    source  = pure . fst
    viewTerm :: (Term, Maybe Term) -> Term
    viewTerm (term, Nothing) = term
    viewTerm (_, Just term)  = term

-- Multistep Evaluation Function
multiStepEval :: Term -> Term
multiStepEval t = maybe t multiStepEval (singleEval t)
