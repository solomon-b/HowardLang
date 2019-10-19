{-# LANGUAGE DeriveFoldable #-}
module TypedLambdaCalcInitial.Types where

import Data.List

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
  deriving Show

data Type = Func Type Type | Boo
  deriving (Eq, Show)

data Binding = NameBind | VarBind Type
  deriving (Eq, Show)

type Context = SnocList (Varname, Binding)


----------------
--- SnocList ---
----------------
-- This is used for more natural lookups of DeBruijn indices
-- from the context.

data SnocList a = Nil | Snoc (SnocList a) a
  deriving (Show, Foldable)

infixl 9 !!!
(!!!) :: SnocList a -> Int -> a
(!!!) Nil i = error "Index too large."
(!!!) (Snoc xs x) 0 = x
(!!!) (Snoc xs x) i = xs !!! (i - 1)

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

addBinding :: Context -> Varname -> Binding -> Context
addBinding ctx var bnd = Snoc ctx (var, bnd)

-- TODO: Make these safer
-- UNSAFE!
getTypeFromContext :: Context -> DeBruijn -> Type
getTypeFromContext ctx i =
  case getBinding ctx i of
    VarBind t -> t
    _ -> error "Wrong kind of binding for variable"

-- UNSAFE!
getBinding :: Context -> Int -> Binding
getBinding xs i = snd $ xs !!! i

typeof :: Context -> Term -> Type
typeof ctx (Var i) = getTypeFromContext ctx i
typeof ctx (Abs var ty t2) = Func ty (typeof (Snoc ctx (var, VarBind ty)) t2)
typeof ctx (App t1 t2) =
  let (Func ty1 ty2) = typeof ctx t1
  in if typeof ctx t2 == ty1
     then ty2
     else error "ill typed yo"
typeof ctx Tru = Boo
typeof ctx Fls = Boo
typeof ctx (If t1 t2 t3) | typeof ctx t1 == Boo = if typeof ctx t2 == typeof ctx t3
                                                  then typeof ctx t2
                                                  else error "ill typed yo"
typeof _ _ = error "ill typed yo"
