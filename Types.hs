module TypedLambdaCalcInitial.Types where

type Varname = String
type DeBruijn = Int
type ContextLength = Int

type OriginalTerm = Term
type NewTerm = Term

data Term
  = Var DeBruijn
  | Abs Varname Term
  | App Term Term
  | Tru
  | Fls
  | If Term Term Term
  deriving Show

data Type = Func Type Type | Boo
  deriving Show


data Binding = NameBind | VarBind Type

type Context = [(Varname, Binding)]

addBinding :: Context -> Varname -> Binding -> Context
addBinding ctx var bnd = (var, bnd) : ctx

-- UNSAFE!
getTypeFromContext :: Context -> Varname -> Type
getTypeFromContext ctx var =
  case lookup var ctx of
    Just (VarBind t) -> t
    _ -> error "Wrong kind of binding for variable"

-- UNSAFE!
getBinding :: Context -> Int -> Binding
getBinding xs i = snd $ xs !! i

--typeof :: Context -> Term -> Type
--typeof ctx (Var i) = getTypeFromContext ctx i
