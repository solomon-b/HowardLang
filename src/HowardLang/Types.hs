{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
module HowardLang.Types where

import Control.Exception (Exception)

import Data.Data
import Data.Function

import Data.Functor.Foldable.TH
--import Language.Haskell.TH
--import GHC.Generics (Generic)

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
  | Z -- TODO: Remove nats when I have casing on rec types and data types/alias bindings
  | S Term
  | Case Term Term Varname Term
  | Unit
  | As Term Type
  | Let Varname Term Term
  | Pair Term Term -- NOTE: Should I remove pairs?
  | Fst Term
  | Snd Term
  | Tuple [(Varname, Term)]
  | Get Term Varname
  | Record [(Varname, Term)]
  | Tag String Term
  | VariantCase Term [(Tag, Maybe Binder, Term)]
  | FixLet Term
  | Roll Type Term
  | Unroll Type Term
  deriving (Show, Eq, Data)

data Type
  = FuncT Type Type
  | BoolT
  | NatT
  | UnitT
  | PairT Type Type
  | TupleT [Type]
  | RecordT [(Tag, Type)]
  | VariantT [(Tag, Type)]
  | FixT Varname Type
  | VarT DeBruijn
  deriving (Show, Data, Eq)

makeBaseFunctor ''Term
makeBaseFunctor ''Type

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
newtype TypeErr = TypeError String deriving (Show, Eq)
data Err = P ParseErr | T TypeErr deriving (Show, Eq)

instance Exception Err

--------------------
--- Misc Helpers ---
--------------------

instance Functor ((,,) a b) where
  fmap f (a,b,c) = (a, b, f c)

isVal :: Term -> Bool
isVal Abs{}       = True
isVal Tru         = True
isVal Fls         = True
isVal Z           = True
isVal Unit        = True
isVal (S n)       = isVal n
isVal (As t1 _)   = isVal t1
isVal (Pair t1 t2) = isVal t1 && isVal t2
isVal (Tuple ts)  = all (isVal . snd) ts
isVal (Record ts)  = all (isVal . snd) ts
isVal (Tag _ t) = isVal t
isVal (Roll _ t)  = isVal t
isVal (Unroll _ (Roll _ _))  = False
isVal (Unroll _ t)  = isVal t
isVal _           = False

isNat :: Term -> Bool
isNat Z = True
isNat (S n) = isNat n
isNat _ = False

isAbs :: Term -> Bool
isAbs Abs{} = True
isAbs _ = False

constrEq :: Data a => a -> a -> Bool
constrEq = (==) `on` toConstr

allEqual :: Eq a => [a] -> Bool
allEqual [] = True
allEqual (x:xs) = all (== x) xs
