module TypedLambdaCalcInitial.Typechecker where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader

import Data.List

import TypedLambdaCalcInitial.Types
import TypedLambdaCalcInitial.PrettyPrinter

--------------------
--- Type Checker ---
--------------------

newtype TypecheckT m a =
  TypecheckT { unTypecheckT :: ExceptT Err (ReaderT Context m) a }
  deriving (Functor, Applicative, Monad, MonadReader Context, MonadError Err)

type TypecheckM a = TypecheckT Identity a

runTypecheckT :: Context -> TypecheckT m a -> m (Either Err a)
runTypecheckT gamma = flip runReaderT gamma . runExceptT . unTypecheckT

runTypecheckM :: Context -> TypecheckT Identity a -> Either Err a
runTypecheckM gamma = runIdentity . runTypecheckT gamma

getIndexFromContext :: Context -> Varname -> Maybe DeBruijn
getIndexFromContext ctx var = find (\el -> var == fst el) ctx >>= flip elemIndex ctx

addBinding :: Context -> Varname -> Type -> Context
addBinding ctx var bnd = (var, bnd) : ctx

-- TODO: Make these safer
-- UNSAFE!
getBinding :: Context -> Int -> Type
getBinding xs i = snd $ xs !! i

typecheck ::
  ( MonadError Err m , MonadReader Context m) => Term -> m Type
typecheck (Var i) = asks (flip getBinding i)
typecheck (Abs var ty t2) = do
  ty2 <- local ((:) (var, ty)) (typecheck t2)
  pure $ FuncT ty ty2
typecheck (App t1 t2) = typecheck t1 >>= \case
  FuncT ty1 ty2 -> do
    ty2' <- typecheck t2
    if ty2' == ty1
      then pure ty2
      else throwError $ T $ typeErr t1 ty1 ty2'
  ty -> throwError $ T $ TypeError $ show t1 ++ " :: " ++ show ty ++ " is not a function"
typecheck Tru = pure BoolT
typecheck Fls = pure BoolT
typecheck (If t1 t2 t3) = typecheck t1 >>= \case
  BoolT -> do
    ty2 <- typecheck t2
    ty3 <- typecheck t3
    if ty2 == ty3
      then pure ty2
      else throwError $ T $ typeErr t2 ty2 ty3
  ty1 -> throwError $ T $ typeErr t1 ty1 BoolT
typecheck Z = pure NatT
typecheck (S t) = typecheck t >>= \case
  NatT -> pure NatT
  ty -> throwError $ T $ typeErr t ty NatT
typecheck (Case n z v s) = typecheck n >>= \case
  NatT -> do
    zTy <- typecheck z
    sTy <- local ((:) (v, zTy)) (typecheck s)
    if zTy == sTy
      then pure sTy
      else throwError $ T $ typeErr z zTy sTy
  ty -> throwError $ T $ typeErr n ty NatT
typecheck Unit = pure UnitT
typecheck (As t1 ty) =
  typecheck t1 >>= \ty1' ->
    if ty1' == ty
       then pure ty
       else throwError $ T $ typeErr t1 ty1' ty
--typecheck (Let v t1 t2) = typecheck t1 >>= \ty1 -> local ((:) (v, ty1)) (typecheck t2)
typecheck (Let v t1 t2) = do
  ty1 <- typecheck t1
  local ((:) (v, ty1)) (typecheck t2)
typecheck (Pair t1 t2) = do
  ty1 <- typecheck t1
  ty2 <- typecheck t2
  pure $ PairT ty1 ty2
typecheck (Fst (Pair t1 _)) = typecheck t1
typecheck (Fst t1) = typecheck t1 >>= \case
  (PairT ty1 _) -> pure ty1
  ty -> (throwError $ T $ TypeError $ "Expected a Pair but got: " ++ show ty)
typecheck (Snd (Pair _ t2)) = typecheck t2
typecheck (Snd t) = typecheck t >>= \case
  (PairT _ ty2) -> pure ty2
  ty -> (throwError $ T $ TypeError $ "Expected a Pair but got: " ++ show ty)
--typecheck (Tuple ts) = pure . TupleT $ traverse typecheck ts

-- TODO: FIX BUG IN PRETTY PRINTER OR REPLACE PRETTY PRINTER
typeErr :: Term -> Type -> Type -> TypeErr
typeErr t1 ty1 ty2 = TypeError $
  "Type Error:\n\r" ++
  "Expected Type: " ++ show ty2 ++ "\n\r" ++
  "Actual Type: "   ++ show ty1 ++ "\n\r" ++
  "For Term: "      ++ show t1 -- pretty t1


{-
TODO: Fix this fun typechecker bug:
λ> (\f:Nat->Nat.\n:Nat.let x = case n of Z => (\z:Nat.\q:Nat.n) | (S m) => (\h:Nat.\z:Nat.m) in x)
Type Error:
Expected Type: Nat -> (Nat -> (Nat -> (Nat -> Nat)))
Actual Type: Nat -> (Nat -> Nat)
For Term: Abs "z" Nat (Abs "q" Nat (Var 2))

I expect the overall expression to be:
`(Nat -> Nat) -> Nat -> Nat -> Nat -> Nat`,

And for the subexpression being reported, the actual type should be the expected type.
-}