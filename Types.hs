{-# LANGUAGE DeriveDataTypeable #-}
module TypedLambdaCalcInitial.Types where

import Control.Exception (Exception)

import Data.List (intersperse)
import Data.Data
import Data.Function
--import qualified Data.Text as T
--import Data.Text.Prettyprint.Doc

import Text.Megaparsec

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
  | Tag Tag Term Type
  | VariantCase Term [(Tag, Maybe Binder, Term)] -- [(binder, tag)]
  | Fix Term
  | Roll Type Term
  | Unroll Type Term
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

--instance Show Type where
--  show BoolT = "Bool"
--  show NatT  = "Nat"
--  show UnitT = "Unit"
--  show (FuncT f1@(FuncT _ _) f2@(FuncT _ _)) = "(" ++ show f1 ++ ")" ++
--                                               " -> " ++ "(" ++ show f2 ++ ")"
--  show (FuncT f1@(FuncT _ _) t2) = "(" ++ show f1 ++ ")" ++ " -> " ++ show t2
--  show (FuncT t1 f2@(FuncT _ _)) = show t1 ++ " -> " ++ "(" ++ show f2 ++ ")"
--  show (FuncT t1 t2) = show t1 ++ " -> " ++ show t2
--  show (PairT t1 t2) = "<" ++ show t1 ++ ", " ++ show t2 ++ ">"
--  show (TupleT ts) = let tys = foldr1 (\a b -> a ++ ", " ++ b) $ show <$> ts in "[" ++ tys ++ "]"
--  show (RecordT ts) = let tys = foldr1 (\a b -> a ++ ", " ++ b) $ show <$> ts in "{" ++ tys ++ "}"
--  show (SumT left right) = "Sum " ++ show left ++ " " ++ show right
--  show v@(VariantT _) = showVariant v
--  -- TODO: Write a proper show instance for FixT
--  show (FixT var ty) = "FixT " ++ var ++ " " ++ show ty
--  show (VarT i) = "VarT " ++ show i

showVariant :: Type -> String
showVariant (VariantT tys) = unwords . intersperse "|" $ f <$> tys
  where
    f :: (Varname, Type) -> String
    f (var, UnitT) = var
    f (var, ty) = var ++ " " ++ show ty
{-
instance Pretty Type where
  pretty = viaShow
-}

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
isVal c (Tag _ t _) = isVal c t
isVal c (Roll _ t)  = isVal c t
isVal c (Unroll _ (Roll _ _))  = False
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

---- Recursive Type Testing:

-- Binary Sum
listT :: Type
listT = FixT "listT" (SumT UnitT $ PairT NatT $ VarT 0)

nil :: Term
nil = Roll listT (InL Unit (SumT UnitT $ PairT NatT listT))

cons :: Term
cons = Abs "x" NatT . Abs "xs" listT .
       Roll listT $ InR (Pair (Var 1) (Var 0)) (SumT UnitT $ PairT NatT listT)

-- SumCase Term Term Binder Term Binder
sumTest :: Term
sumTest = SumCase (Unroll listT $ nil) Z "nil" (Fst $ Var 0) "x"

hd :: Term
hd = Abs "xs" listT $
     SumCase (Unroll listT $ Var 0) Z "nil" (Fst $ Var 0) "x"

consTest :: Term
consTest = App (App cons (S Z)) (App (App cons Z) nil)

hdTest :: Term
hdTest = App hd consTest

-- Variant Form

listTV :: Type
listTV = FixT "listTV" (VariantT [("Nil", UnitT), ("Cons", TupleT [NatT, VarT 0])])

tagNil :: Term
tagNil = (Tag "Nil" Unit (VariantT [("Nil", UnitT), ("Cons", TupleT [NatT, listTV])]))

nilV :: Term
nilV = Roll listTV (Tag "Nil" Unit (VariantT [("Nil", UnitT), ("Cons", TupleT [NatT, listTV])]))

vTerm :: Term
vTerm = Tag "Just" Z (VariantT [("Nothing", UnitT),("Just", NatT)])

variant :: Term
variant = Abs "x" (VariantT [("Nothing", UnitT), ("Just", NatT)]) $
          VariantCase (Var 0) [("Nothing", Nothing, Z), ("Just", Just "x", Var 0)]

unroll :: Term
unroll = (Unroll (VariantT [("Nothing", UnitT), ("Just", NatT)]) vTerm)

variant' :: Term
variant' = Abs "x" (VariantT [("Nothing", UnitT), ("Just", NatT)]) $
          VariantCase unroll [("Nothing", Nothing, Z), ("Just", Just "x", Var 0)]

consV :: Term
consV = Abs "x" NatT . Abs "xs" listTV .
       Roll listTV $ Tag "Cons" (Tuple [("0", Var 1), ("1", Var 0)]) (VariantT [("Nil", UnitT), ("Cons", TupleT [NatT, listTV])])

hdV :: Term
hdV = Abs "xs" listTV $
      VariantCase (Unroll listTV $ Var 0) [("Nil", Nothing, Z), ("Cons", Just "y", Fst $ Var 0)]

consTestV :: Term
consTestV = App (App consV (S Z)) (App (App consV Z) nilV)

hdTestV :: Term
hdTestV = App hdV consTestV
