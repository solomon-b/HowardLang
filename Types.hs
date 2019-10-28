{-# LANGUAGE DeriveDataTypeable #-}
module TypedLambdaCalcInitial.Types where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader

import Data.Data
import Data.List
--import qualified Data.Text as T
--import Data.Text.Prettyprint.Doc

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
  | As Term Type
  | Let Varname Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  deriving Eq

instance Show Term where
  show (Var i) = show i
  show (Abs v ty t1) = "(λ " ++ v ++ " : " ++ show ty ++ ". " ++ show t1 ++ ")"
  show (App t1 t2) = show t1 ++ " " ++ show t2
  show Tru = "True"
  show Fls = "False"
  show (If t1 t2 t3) = "if: " ++ show t1 ++ " then: " ++ show t2 ++ " else: " ++ show t3
  show Z = "0"
  show (S t) = "S " ++ show t
  show (Case t1 t2 v t3) = "case "   ++ show t1 ++ " of:" ++
                           " Z => " ++ show t2 ++ " | "  ++
                           " S "    ++ v       ++ " => " ++ show t3
  show Unit = "Unit"
  show (As t1 ty) = show t1 ++ " as " ++ show ty
  show (Let v t1 t2) = "Let " ++ v ++ " = " ++ show t1 ++ " in " ++ show t2
  show (Pair t1 t2) = "{" ++ show t1 ++ ", " ++ show t2 ++ "}"
  show (Fst t) = "fst " ++ show t
  show (Snd t) = "snd " ++ show t
{-
-- TODO: Learn how to use `prettyprinter` and replace my bespoke printer
instance Pretty Term where
  pretty = viaShow
-}

data Type = FuncT Type Type | BoolT | NatT | UnitT | PairT Type Type
  deriving Eq

instance Show Type where
  show BoolT = "Bool"
  show NatT  = "Nat"
  show UnitT = "Unit"
  show (FuncT f1@(FuncT _ _) f2@(FuncT _ _)) = "(" ++ show f1 ++ ")" ++
                                               " -> " ++ "(" ++ show f2 ++ ")"
  show (FuncT f1@(FuncT _ _) t2) = "(" ++ show f1 ++ ")" ++ " -> " ++ show t2
  show (FuncT t1 f2@(FuncT _ _)) = show t1 ++ " -> " ++ "(" ++ show f2 ++ ")"
  show (FuncT t1 t2) = show t1 ++ " -> " ++ show t2
  show (PairT t1 t2) = show t1 ++ " X " ++ show t2

{-
instance Pretty Type where
  pretty = viaShow
-}

-- | Context Types
type Bindings = [Varname]
type Context = [(Varname, Type)]

-- | Error Types
data UnboundError = UnboundError String
  deriving (Eq, Data, Typeable, Ord, Read, Show)

instance ShowErrorComponent UnboundError where
  showErrorComponent (UnboundError msg) =
    "Unbound error: " ++ msg

type ParseErr = ParseErrorBundle String UnboundError
data TypeErr = TypeError String deriving Show

data Err = P ParseErr | T TypeErr deriving Show

instance Exception Err


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

getIndexFromContext :: Context -> Varname -> Maybe DeBruijn
getIndexFromContext ctx var = find (\el -> var == fst el) ctx >>= flip elemIndex ctx

addBinding :: Context -> Varname -> Type -> Context
addBinding ctx var bnd = (var, bnd) : ctx

-- TODO: Make these safer
-- UNSAFE!
getBinding :: Context -> Int -> Type
getBinding xs i = snd $ xs !! i

typecheck ::
  ( MonadError Err m
  , MonadReader Context m) =>
  Term -> m Type
typecheck (Var i) = asks (flip getBinding i)
typecheck (Abs var ty t2) = do
  ty2 <- local ((:) (var, ty)) (typecheck t2)
  pure $ FuncT ty ty2
typecheck (App t1 t2) = typecheck t1 >>= \case
  FuncT ty1 ty2 -> do
    ty1' <- typecheck t2
    if ty1' == ty1
      then pure ty2
      else throwError $ T $ typeMismatch t1 ty1 t2 ty1'
  ty -> throwError $ T $ TypeError $ show t1 ++ " :: " ++ show ty ++ "is not a function"
typecheck Tru = pure BoolT
typecheck Fls = pure BoolT
typecheck (If t1 t2 t3) = typecheck t1 >>= \case
  BoolT -> do
    ty2 <- typecheck t2
    ty3 <- typecheck t3
    if ty2 == ty3
      then pure ty2
      else throwError $ T $ typeMismatch t2 ty2 t3 ty3
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
      else throwError $ T $ typeMismatch z zTy s sTy
  ty -> throwError $ T $ typeErr n ty NatT
typecheck Unit = pure UnitT
typecheck (As t1 ty) = typecheck t1 >>= \ty1' ->
                       if ty1' == ty
                          then pure ty
                          else throwError $ T $ typeErr t1 ty1' ty
typecheck (Let _ t1 t2) = typecheck t1 >> typecheck t2 -- Is this suspect?
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


typeMismatch :: Term -> Type -> Term -> Type -> TypeErr
typeMismatch t1 ty1 t2 ty2 = TypeError (show t1 ++ " :: " ++ show ty1 ++ " does not match " ++ show t2 ++ " :: " ++ show ty2)

typeErr :: Term -> Type -> Type -> TypeErr
typeErr t1 ty1 t2 = TypeError $ show t1 ++ " :: " ++ show ty1 ++ "does not match " ++ show t2
