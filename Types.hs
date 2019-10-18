module TypedLambdaCalcInitial.Types where

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

type Context = [(Varname, Binding)]

addBinding :: Context -> Varname -> Binding -> Context
addBinding ctx var bnd = (var, bnd) : ctx

-- TODO: Make these safer
-- UNSAFE!
getTypeFromContext :: Context -> DeBruijn -> Type
getTypeFromContext ctx i =
  case getBinding ctx i of
    VarBind t -> t
    _ -> error "Wrong kind of binding for variable"

-- UNSAFE!
getBinding :: Context -> Int -> Binding
getBinding xs i = snd $ xs !! i

typeof :: Context -> Term -> Type
typeof ctx (Var i) = getTypeFromContext ctx i
typeof ctx (Abs var ty t2) = Func ty (typeof ((var, VarBind ty):ctx) t2)
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



