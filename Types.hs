module TypedLambdaCalcInitial.Types where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import Data.List
import Data.Void

import Text.Megaparsec

type Varname = String
type DeBruijn = Int
type ContextLength = Int

data Term
  = Var DeBruijn
  | Abs Varname Type Term
  | App Term Term
  | Tru
  | Fls
  | If Term Term Term
  | Z
  | S Term
  | Case Term Term Varname Term
  | Unit
  deriving (Show, Eq)

data Type = FuncT Type Type | BoolT | NatT | UnitT
  deriving Eq

instance Show Type where
  show BoolT = "Bool"
  show NatT  = "Nat"
  show UnitT = "Unit"
  show (FuncT f1@(FuncT _ _) f2@(FuncT _ _)) = "(" ++ show f1 ++ ")" ++ " -> " ++ "(" ++ show f2 ++ ")"
  show (FuncT f1@(FuncT _ _) t2) = "(" ++ show f1 ++ ")" ++ " -> " ++ show t2
  show (FuncT t1 f2@(FuncT _ _)) = show t1 ++ " -> " ++ "(" ++ show f2 ++ ")"
  show (FuncT t1 t2) = show t1 ++ " -> " ++ show t2

-- | Context Types
type Bindings = SnocList Varname
type Context = SnocList (Varname, Type)

-- | Error Types
type ParseErr = ParseErrorBundle String Void
data TypeErr = TypeError deriving Show

data Err = P ParseErr | T TypeErr deriving Show

instance Exception Err


----------------
--- SnocList ---
----------------
-- TODO: Do I really need snoc lists?

data SnocList a = Nil | Snoc (SnocList a) a
  deriving (Show, Foldable)

infixl 9 !!!
(!!!) :: SnocList a -> Int -> a
(!!!) Nil _ = error "Index too large."
(!!!) (Snoc _ x) 0 = x
(!!!) (Snoc xs _) i = xs !!! (i - 1)

snocIndex :: Eq a => SnocList a -> a -> Maybe Int
snocIndex xs var = f xs var 0
  where
    f :: Eq a => SnocList a -> a -> Int -> Maybe Int
    f Nil _ _ = Nothing
    f (Snoc xs' x') var' i' = if x' == var' then Just i' else f xs' var' (i'+1)

getIndexFromContext :: Context -> Varname -> Maybe DeBruijn
getIndexFromContext ctx var = find (\el -> var == fst el) ctx >>= snocIndex ctx


---------------------
--- Type Checking ---
---------------------
-- TODO: Move this into its own module?


newtype TypecheckT m a =
  TypecheckT { unTypecheckT :: ExceptT Err (ReaderT Context m) a }
  deriving (Functor, Applicative, Monad, MonadReader Context, MonadError Err)

type TypecheckM a = TypecheckT Identity a

runTypecheckT :: Context -> TypecheckT m a -> m (Either Err a)
runTypecheckT gamma = flip runReaderT gamma . runExceptT . unTypecheckT

runTypecheckM :: Context -> TypecheckT Identity a -> Either Err a
runTypecheckM gamma = runIdentity . runTypecheckT gamma


addBinding :: Context -> Varname -> Type -> Context
addBinding ctx var bnd = Snoc ctx (var, bnd)

-- TODO: Make these safer
-- UNSAFE!
getBinding :: Context -> Int -> Type
getBinding xs i = snd $ xs !!! i


typecheck ::
  ( MonadError Err m
  , MonadReader Context m) =>
  Term -> m Type
typecheck (Var i) = asks (flip getBinding i)
typecheck (Abs var ty t2) = do
  ty2 <- local (flip Snoc (var, ty)) (typecheck t2)
  pure $ FuncT ty ty2
typecheck (App t1 t2) = typecheck t1 >>= \case
  FuncT ty1 ty2 -> do
    ty1' <- typecheck t2
    if ty1' == ty1
      then pure ty2
      else throwError $ T TypeError
  _ -> throwError $ T TypeError
typecheck Tru = pure BoolT
typecheck Fls = pure BoolT
typecheck (If t1 t2 t3) = typecheck t1 >>= \case
  BoolT -> do
    ty2 <- typecheck t2
    ty3 <- typecheck t3
    if ty2 == ty3
      then pure ty2
      else throwError $ T TypeError
  _ -> throwError $ T TypeError
typecheck Z = pure NatT
typecheck (S t) = typecheck t >>= \case
  NatT -> pure NatT
  _ -> throwError $ T TypeError
typecheck (Case l m _ n) = typecheck l >>= \case
  NatT -> do
    mTy <- typecheck m
    nTy <- typecheck n
    if mTy == nTy
      then pure nTy
      else throwError $ T TypeError
  _ -> throwError $ T TypeError
typecheck Unit = pure UnitT
