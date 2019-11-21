{-# LANGUAGE RankNTypes #-}
module Roundtrip where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except

import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Internal.Gen as G
import Hedgehog.Range

import HowardLang.Parser
import HowardLang.Types
import HowardLang.PrettyPrinter

-----------------------------------
--- Bidirectional Parsing Tests ---
-----------------------------------
-- TODO: Revisit this module in its entirety

bidirectional :: Property
bidirectional = property $ do
  t1 <- Gen.sample $ runReaderT genAbs []
  let res = runParse $ pretty t1
  Right t1 === res


testProperties :: IO Bool
testProperties = check bidirectional

sample gen = Gen.sample $ runReaderT gen []

----------------------------
--- Expression Generator ---
----------------------------

-- Experimental!!!!
-- This does produce well typed terms, however, it leaves a lot to be desired as
-- far as distribution of values

-- look into this hedgehog example:
-- https://github.com/hedgehogqa/haskell-hedgehog/blob/master/hedgehog-example/src/Test/Example/STLC.hs

-- look into this paper:
-- http://publications.lib.chalmers.se/records/fulltext/195847/local_195847.pdf

-- Our Algorithm:
-- 1. Gen an abstraction
-- 2. If if there are functions in scope:
--      then, choose between abstraction, var, and application
--      else, choose between abstraction and var
-- 3. If application:
--      then, pick a func and a matching param in context
--      if not matches, then create an abstraction that takes
--      a type that is in scope, then apply that abstraction
--      to the in scope param.

-- Alternate step 3 idea: that may produce better distribution:
-- 3. If application:
--      a. Find an Abstraction in scope, if none then create one that matches an
--         in scope value.
--      b. Find a var in scope, if none of the correct type then use a base value.

type Generator a = forall m. (MonadReader Context m, MonadGen m) => m a

type FuncT = (Varname, Type, Int)
type ValT = (Varname, Type, Int)

viableApplications :: MonadError () m => [FuncT] -> [ValT] -> m [(FuncT, ValT)]
viableApplications fs vs =
  let res = do
        f <- fs
        v <- vs
        guard (matches f v)
        return (f, v)
  in if null res then throwError () else pure res
  where
    matches :: FuncT -> ValT -> Bool
    matches (_, FuncT ty1 _, _) (_,ty2, _) = ty1 == ty2
    matches _ _ = False

genApp' :: (MonadError () m, MonadReader Context m, MonadGen m) => m Term
genApp' = do
  funcs <- findFuncs =<<  ask
  vals <- findVals =<<  ask
  ((_,_, i), (_,_,j)) <- Gen.element =<< viableApplications funcs vals
  pure $ App (Var i) (Var j)


findTerms :: Type -> Context -> Maybe [(Varname, Type, Int)]
findTerms ty xs = f xs 0 []
  where
    f [] _ [] = Nothing
    f [] _ zs = Just zs
    f (y:ys) i zs = if ty == snd y
                       then f ys (i+1) ((fst y, snd y, i) : zs)
                       else f ys (i+1) zs

-- Returns all FuncTs from the context with their DeBruijn indices
findFuncs :: MonadError () m => Context -> m [(Varname, Type, Int)]
findFuncs xs = f xs 0 []
  where
    f [] _ [] = throwError ()
    f [] _ zs = pure zs
    f (y:ys) i zs = case snd y of
      FuncT _ _ -> f ys (i+1) ((fst y, snd y, i) : zs)
      _ -> f ys (i+1) zs

findVals :: MonadError () m => Context -> m [(Varname, Type, Int)]
findVals xs = f xs 0 []
  where
    f [] _ [] = throwError ()
    f [] _ zs = pure zs
    f (y:ys) i zs = case snd y of
      FuncT _ _ -> f ys (i+1) zs
      _ -> f ys (i+1) ((fst y, snd y, i) : zs)

-- Selects a random FuncT from the context, returning a `Var` with its type
pickFunc :: Generator (Maybe (Term, Type))
pickFunc = do
  -- Find a random free variable with type Func
  mctx <- asks findFuncs
  case mctx of
    Just ctx -> do
      (_, ty, i) <- Gen.element ctx
      pure . Just $ (Var i, ty)
    Nothing -> pure Nothing

-- Picks a random term from context with the desired type
pickFreeVar :: Type -> Generator (Maybe Term)
pickFreeVar ty = do
  mctx <- asks (findTerms ty)
  case mctx of
    Just ctx -> do
      (_, _, i) <- Gen.element ctx
      pure . Just $ Var i
    Nothing -> pure Nothing

-- Gen a Var with a random in scope DeBruijn Index
genVar :: Generator Term
genVar = do
  ctx <- ask
  Var <$> Gen.integral (constant 0 ((length ctx) - 1))

-- Generate a random type
genType :: Generator Type
genType = Gen.frequency [(2, pure NatT), (2, pure BoolT), (1, FuncT <$> genType <*> genType)]

-- Generate a random lambda abstraction
genAbs :: Generator Term
genAbs = fst <$> genAbsTy

-- Generate a random Abstraction with a set depth
genAbsDepth :: Int -> Term -> Generator Term
genAbsDepth 0 t = pure t
genAbsDepth i t = do
  var <- genVarname
  ty <-  genType
  t' <- genAbsDepth (i - 1) t
  pure $ Abs var ty t'

-- Generate a lambda expression and return its input type
genAbsTy :: Generator (Term, Type)
genAbsTy = do
  var  <- genVarname
  ty   <- genType
  -- add the new free variable (with its type) to the new scope
  term <- local (updateContext (var, ty)) genTerm
  pure $ (Abs var ty term, ty)

genPair :: Generator Term
genPair = do
  t1 <- genTerm
  t2 <- genTerm
  pure $ Pair t1 t2

-- When generating an Application our choices are:
-- For t1:
-- 1. Any in scope variable bound to a function IFF there is an in scope variable to apply to it
-- 2. A new Abstraction
genApp :: Generator Term
genApp = do
  res <- runExceptT genApp'
  case res of
    Left _ -> genAbs
    Right t1 -> pure t1

genNat :: Generator Term
genNat = Gen.frequency [ (1, pure Z), (4, S <$> genNat)]

genBool :: Generator Term
genBool = Gen.element [Tru, Fls]

-- TODO: Generate a term with a desired type and depth:
genDesiredTerm :: Type -> Int ->  Generator Term
genDesiredTerm NatT depth = pure Z
genDesiredTerm BoolT depth = pure Tru

-- TODO: Not well typed currently
-- When generating an If:
-- t1 must evaluate to a `Bool`
-- t2 and t3 must have the same type
genIf :: Generator Term
genIf = do
  t1 <- genBool
  t2 <- genTerm
  t3 <- genTerm
  pure $ If t1 t2 t3

genString :: Generator String
genString = sequence $ replicate 10 Gen.lower

genVarname :: Generator Varname
genVarname = do
  ctx <- ask
  G.filterT (notIn ctx) genString

notIn :: Context -> String -> Bool
notIn ctx v = maybe True (const False) (lookup v ctx)

genDesiredAbs :: Type -> Generator Term
genDesiredAbs ty = do
  -- When Generating an Abstraction, add the new free variable (with its type) to
  -- the new scope
  var  <- genVarname
  term <- local (updateContext (var, ty)) genTerm
  pure $ Abs var ty term

genTerm :: Generator Term
genTerm = Gen.frequency $
    [ (4, genAbs)
    , (4, genVar)
    , (6, genApp)
    , (1, genPair)
    , (1, genNat)
    , (1, genBool)
    , (1, pure Unit)
    ]
