{-# LANGUAGE DeriveDataTypeable #-}
module HowardLang.Types where

import Control.Exception (Exception)

import Data.Data
import Data.Function

import Text.Megaparsec

type Name = String
type Tag = String
type Binder = String
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
  | Tuple [(Varname, Term)]
  | Get Term Varname -- Get Tuple Nat
  | Record [(Varname, Term)]
  | InL Term Type
  | InR Term Type
  | SumCase Term Term Binder Term Binder
  | Tag String Term
  | VariantCase Term [(Tag, Maybe Binder, Term)] -- [(binder, tag)]
  | Fix Term
  | Roll Type Term
  | Unroll Type Term
  deriving (Show, Eq)

data Type
  = FuncT Type Type
  | BoolT
  | NatT
  | UnitT
  | PairT Type Type
  | TupleT [Type]
  | RecordT [(Tag, Type)]
  | SumT Type Type
  | VariantT [(Tag, Type)]
  | FixT Varname Type
  | VarT DeBruijn
  deriving (Show, Data, Eq)

-- TODO: Implement a Context for type aliases!
-- https://gist.github.com/ssbothwell/3a263a13df31942c292585d608c3892b

-- | Context Types
type Bindings = [Varname]
type Context = [(Varname, Type)]

updateContext :: (Varname, Type) -> Context -> Context
updateContext t ctx = t:ctx

-- | Error Types
newtype UnboundError = UnboundError String
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

instance Functor ((,,) a b) where
  fmap f (a,b,c) = (a, b, f c)

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
isVal c (Tuple ts)  = all (isVal c . snd) ts
isVal c (Record ts)  = all (isVal c . snd) ts
isVal c (InL t _)   = isVal c t
isVal c (InR t _)   = isVal c t
isVal c (Tag _ t) = isVal c t
isVal c (Roll _ t)  = isVal c t
isVal _ (Unroll _ (Roll _ _))  = False
isVal c (Unroll _ t)  = isVal c t
-- TODO: Should Lets and Cases be considered values if their terms are fully reduced? I think so?
isVal _ _           = False

isNat :: Term -> Bool
isNat Z = True
isNat (S n) = isNat n
isNat _ = False

constrEq :: Data a => a -> a -> Bool
constrEq = (==) `on` toConstr

allEqual :: Eq a => [a] -> Bool
allEqual [] = True
allEqual (x:xs) = all (== x) xs

-- TODO: Fix this bug:
-- λ> let x = {foo=inr True : Sum Nat Bool} in (get x[foo])
-- typedLCI: Prelude.!!: index too large
