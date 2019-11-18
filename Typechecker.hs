module TypedLambdaCalcInitial.Typechecker where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader

import Data.List
import Data.Maybe (mapMaybe)

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

bindLocalTags :: (MonadError Err m , MonadReader Context m) =>
  [(Tag, Type)] -> (Tag, Binder, Term) -> m Type
bindLocalTags ty1 (tag, bndr, tC) = case lookup tag ty1 of
  Just tyC -> bindLocalVar bndr tyC tC
  Nothing -> throwTypeError' $ "Expected type: " ++ show (VariantT ty1)

sequencePattern :: (Tag, Maybe Binder, Term) -> Maybe (Tag, Binder, Term)
sequencePattern (tag, Just bndr, trm) = Just (tag, bndr, trm)
sequencePattern (_, Nothing, _) = Nothing

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
-- TODO: Typechecker is passing `{foo=1, foo=True}`
typecheck (Record ts) = traverse (\(_,t) -> typecheck t) ts >>= pure . RecordT
typecheck (InL t1 ty@(SumT tyL _)) = typecheck t1 >>= \ty1 ->
  if ty1 == tyL
  then pure ty
  else throwTypeError t1 ty1 tyL -- TODO: Improve this error, it does not reference the sum type.
typecheck (InL _ ty) = throwTypeError' $ "Type Error: " ++ show ty ++ " is not a Sum type."
typecheck (InR t1 ty@(SumT _ tyR)) = typecheck t1 >>= \ty1 ->
  if ty1 == tyR
  then pure ty
  else throwTypeError t1 ty1 tyR -- TODO: Improve this error, it does not reference the sum type.
typecheck (InR _ ty) = throwTypeError' $ "Type Error: " ++ show ty ++ " is not a Sum type."
typecheck (SumCase t tL vL tR vR) = typecheck t >>= \case
  (SumT l r) -> do
    tyL <- bindLocalVar vL l tL
    tyR <- bindLocalVar vR r tR
    if tyL == tyR
    then pure tyR
    else throwTypeError tL tyR tyL
  ty -> throwTypeError' $ "Expected a Sum Type but got: " ++ show ty
typecheck t@(Tag tag t1 ty) = typecheck t1 >>= \ty1 ->
  case ty of
    VariantT tys ->
      case lookup tag tys of
        Just ty' | ty' == ty1 -> pure ty
        _ -> throwTypeError t ty1 ty -- TODO: Improve this error, it does not reference the sum type.
    _ -> throwTypeError t ty1 ty
typecheck (Fix t) = typecheck t >>= \case
  (FuncT ty1 ty2) -> if ty1 == ty2 then pure ty2 else throwTypeError t ty2 ty1
  ty  -> throwTypeError' $ "Type Error: " ++ show ty ++ " is not a function type"
typecheck (VariantCase t1 cases) = typecheck t1 >>= \case
  (VariantT casesT) -> do
    let cases' = mapMaybe sequencePattern cases
    types <- traverse (bindLocalTags casesT) cases'
    if allEqual types
    then pure $ types !! 0
    else throwTypeError' "Type mismatch between cases"
  ty -> throwTypeError' $ "Expected a Variant Type but got: " ++ show ty


------------------------------------------------------------
------ TODO: IMPROVE ERROR MESSAGING MASSIVELY !!!!!! ------
------------------------------------------------------------

throwTypeError :: MonadError Err m => Term -> Type -> Type -> m a
throwTypeError t1 ty1 ty2 = throwError . T . TypeError $
  "Type Error:\n\r" ++
  "Expected Type: " ++ show ty2 ++ "\n\r" ++
  "Actual Type: "   ++ show ty1 ++ "\n\r" ++
  "For Term: "      ++ pretty t1 

throwTypeError' :: MonadError Err m => String -> m a
throwTypeError' = throwError . T . TypeError
