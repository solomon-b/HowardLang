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

-- TODO: Improve error reporting!!!!
natToInt :: MonadError Err m => Term -> m Int
natToInt Z = pure 0
natToInt (S t) = (+1) <$> natToInt t
natToInt _ = throwTypeError' $ "Type Error: Excepted Nat"

bindLocalVar :: (MonadReader Context m, MonadError Err m) => Varname -> Type -> Term -> m Type
bindLocalVar var typ term = local ((:) (var, typ)) (typecheck term)

typecheck ::
  (MonadError Err m , MonadReader Context m) => Term -> m Type
typecheck (Var i) = asks (flip getBinding i)
typecheck (Abs var ty t2) = do
  ty2 <- bindLocalVar var ty t2
  pure $ FuncT ty ty2
typecheck (App t1 t2) = typecheck t1 >>= \case
  FuncT ty1 ty2 -> do
    ty2' <- typecheck t2
    if ty2' == ty1
    then pure ty2
    else throwTypeError t1 ty1 ty2'
  ty -> throwTypeError' $ pretty t1 ++ " :: " ++ show ty ++ " is not a function"
typecheck Tru = pure BoolT
typecheck Fls = pure BoolT
typecheck (If t1 t2 t3) = typecheck t1 >>= \case
  BoolT -> do
    ty2 <- typecheck t2
    ty3 <- typecheck t3
    if ty2 == ty3
      then pure ty2
      else throwTypeError t2 ty2 ty3
  ty1 -> throwTypeError t1 ty1 BoolT
typecheck Z = pure NatT
typecheck (S t) = typecheck t >>= \case
  NatT -> pure NatT
  ty -> throwTypeError t ty NatT
typecheck (Case n z v s) = typecheck n >>= \case
  NatT -> do
    zTy <- typecheck z
    sTy <- bindLocalVar v NatT s
    if zTy == sTy
      then pure sTy
      else throwTypeError z zTy sTy
  ty -> throwTypeError n ty NatT
typecheck Unit = pure UnitT
typecheck (As t1 ty) =
  typecheck t1 >>= \ty1' ->
    if ty1' == ty
       then pure ty
       else throwTypeError t1 ty1' ty
typecheck (Let v t1 t2) = typecheck t1 >>= \ty1 -> bindLocalVar v ty1 t2
typecheck (Pair t1 t2) = do
  ty1 <- typecheck t1
  ty2 <- typecheck t2
  pure $ PairT ty1 ty2
typecheck (Fst (Pair t1 _)) = typecheck t1
typecheck (Fst t1) = typecheck t1 >>= \case
  (PairT ty1 _) -> pure ty1
  ty -> throwTypeError' $ "Expected a Pair but got: " ++ show ty
typecheck (Snd (Pair _ t2)) = typecheck t2
typecheck (Snd t) = typecheck t >>= \case
  (PairT _ ty2) -> pure ty2
  ty -> throwTypeError' $ "Expected a Pair but got: " ++ show ty
typecheck (Tuple ts) = traverse (typecheck . snd) ts >>= pure . TupleT
typecheck (Get (Tuple ts) v) =
  case lookup v ts of
    Just t -> typecheck t
    Nothing -> throwTypeError' "Type Error: Projection failed"
-- TODO: Figure out how to recover these more helpful errors:
-- "Type Error: Index out of range"
-- "Type Error: Expected type Nat for projection"
typecheck (Get (Record ts) v) =
  case lookup v ts of
    Just t -> typecheck t
    Nothing -> throwTypeError' $ "Type Error: No such field " ++ v ++ " in record"
typecheck (Get t1 _) = throwTypeError' $ "Type Error: " ++ pretty t1 ++ " is not a Tuple or Record."
typecheck (Record ts) = traverse (\(_,t) -> typecheck t) ts >>= pure . RecordT
typecheck (InL t1) = flip SumT undefined <$> typecheck t1 -- TODO: How do you determine the type of the other half of the union???
typecheck (InR t1) = SumT undefined <$> typecheck t1      -- TODO: How do you determine the type of the other half of the union???
typecheck (SumCase t tL vL tR vR) =
  case t of
    (InL t1) -> typecheck t1 >>= \ty1 -> bindLocalVar vL ty1 tL
    (InR t1) -> typecheck t1 >>= \ty1 -> bindLocalVar vR ty1 tR
    t1 -> do (show <$> typecheck t1) >>= \ty -> throwTypeError' $ "Expected a Sum Type but got: " ++ ty

throwTypeError :: MonadError Err m => Term -> Type -> Type -> m a
throwTypeError t1 ty1 ty2 = throwError . T . TypeError $
  "Type Error:\n\r" ++
  "Expected Type: " ++ show ty2 ++ "\n\r" ++
  "Actual Type: "   ++ show ty1 ++ "\n\r" ++
  "For Term: "      ++ pretty t1

throwTypeError' :: MonadError Err m => String -> m a
throwTypeError' = throwError . T . TypeError
