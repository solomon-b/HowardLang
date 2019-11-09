{-# LANGUAGE DeriveDataTypeable #-}
module TypedLambdaCalcInitial.Types where

import Control.Exception (Exception)

import Data.Data
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
  | Tuple [Term]
  | Get Term Term -- Get Tuple Nat
  deriving (Show, Eq)


--instance Show Term where
--  show (Var i) = "idx " ++ show i
--  show (Abs v ty t1) = "(λ " ++ v ++ " : " ++ show ty ++ ". " ++ show t1 ++ ")"
--  show (App t1 t2) = "(eval " ++ show t1 ++ " " ++ show t2 ++ ")"
--  show Tru = "True"
--  show Fls = "False"
--  show (If t1 t2 t3) = "if: " ++ show t1 ++ " then: " ++ show t2 ++ " else: " ++ show t3
--  show Z = "0"
--  show (S t) = "S " ++ show t
--  show (Case t1 t2 v t3) = "case "   ++ show t1 ++ " of:" ++
--                           " Z => " ++ show t2 ++ " | "  ++
--                           " S "    ++ v       ++ " => " ++ show t3
--  show Unit = "Unit"
--  show (As t1 ty) = show t1 ++ " as " ++ show ty
--  show (Let v t1 t2) = "Let " ++ v ++ " = " ++ show t1 ++ " in " ++ show t2
--  show (Pair t1 t2) = "{" ++ show t1 ++ ", " ++ show t2 ++ "}"
--  show (Fst t) = "fst " ++ show t
--  show (Snd t) = "snd " ++ show t
--  show (Tuple xs) = "<" ++ intersperse ',' (unwords (show <$> xs)) ++ ">"
--  show (Get t1 t2) = show t2 ++ "[" ++ show t1 ++ "]"
{-
-- TODO: Learn how to use `prettyprinter` and replace my bespoke printer
instance Pretty Term where
  pretty = viaShow
-}

data Type = FuncT Type Type | BoolT | NatT | UnitT | PairT Type Type | TupleT [Type]
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
  show (TupleT ts) = let tys = foldl1 (\b a -> a ++ ", " ++ b) $ show <$> ts in "<" ++ tys ++ ">"

{-
instance Pretty Type where
  pretty = viaShow
-}

-- | Context Types
type Bindings = [Varname]
type Context = [(Varname, Type)]

updateContext :: (Varname, Type) -> Context -> Context
updateContext t ctx = t:ctx

-- | Error Types
data UnboundError = UnboundError String
  deriving (Eq, Data, Typeable, Ord, Read, Show)

instance ShowErrorComponent UnboundError where
  showErrorComponent (UnboundError msg) =
    "Unbound error: " ++ msg

type ParseErr = ParseErrorBundle String UnboundError
data TypeErr = TypeError String deriving (Show, Eq)

data Err = P ParseErr | T TypeErr deriving (Show, Eq)

instance Exception Err


--------------------
--- Misc Helpers ---
--------------------


-- Other then Application, what should not be a value?
isVal :: Context -> Term -> Bool
isVal _ (Abs _ _ _) = True
isVal _ Tru         = True
isVal _ Fls         = True
isVal _ Z           = True
isVal _ Unit        = True
isVal c (S n)       = isVal c n
isVal c (As t1 _)   = isVal c t1
isVal c (Pair t1 t2) = isVal c t1 && isVal c t2
isVal c (Tuple ts)  = all (isVal c) ts
isVal _ _           = False

isNat :: Term -> Bool
isNat Z = True
isNat (S n) = isNat n
isNat _ = False
