module HowardLang.PrettyPrinter where

import Control.Monad.Reader
import Data.List (intersperse)
--import qualified Data.Text.Prettyprint.Doc as P

import HowardLang.Types

----------------------
--- Pretty Printer ---
----------------------

{-
-- TODO
typeToList :: Type -> [Type]
typeToList (FuncT ty1@(FuncT _ _) ty2) = [ty1, ty2]
typeToList (FuncT ty1 ty2@(FuncT _ _)) = [ty1, ty2]
typeToList (FuncT ty1 ty2) = [ty1, ty2]
typeToList ty = pure ty

prettyType :: [P.Doc ann] -> P.Doc ann
prettyType = P.align . P.sep . zipWith (P.<+>) ("::" : repeat "->")

prettyDecl :: P.Pretty a => a -> [P.Doc ann] -> P.Doc ann
prettyDecl n tys = P.pretty n P.<+> prettyType tys
-}

-- TODO: Bug fix. This blows up on `> (\x:Nat. S x)`
showNat :: Term -> String
showNat nat = show $ f nat
  where
    f :: Term -> Int
    f Z = 0
    f (S n) = 1 + f n
    f _ = error "Ooops, typechecker failed to identify an ill typed Nat"

commas :: [String] -> String
commas = foldl1 (\a b -> a ++ ", " ++ b)

class Show a => Pretty a where
  pretty :: a -> String
  pretty = show

instance Pretty Int where

instance Pretty String where
  pretty = id

instance Pretty Type where
  pretty ty = runReader (f ty) []
    where
      f :: Type -> Reader Bindings String
      f BoolT = pure "Bool"
      f NatT  = pure "Nat"
      f UnitT = pure "Unit"
      f (FuncT f1@(FuncT _ _) f2@(FuncT _ _)) = do
        f1' <- f f1
        f2' <- f f2
        pure $ "(" ++ f1'  ++ ")" ++ " -> " ++ "(" ++ f2' ++ ")"
      f (FuncT f1@(FuncT _ _) t2) = do
        f1' <- f f1
        t2' <- f t2
        pure $ "(" ++ f1' ++ ")" ++ " -> " ++ t2'
      f (FuncT t1 f2@(FuncT _ _)) = do
        t1' <- f t1
        f2' <- f f2
        pure $ t1' ++ " -> " ++ "(" ++ f2' ++ ")"
      f (FuncT t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        pure $ t1' ++ " -> " ++ t2'
      f (PairT t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        pure $ "<" ++ t1' ++ ", " ++ t2' ++ ">"
      f (TupleT ts) = do
        ts' <- traverse f ts
        pure $ "(" ++ commas ts' ++ ")"
      f (RecordT ts) = do
        ts' <- traverse (f . snd) ts
        pure $ "{" ++ commas ts' ++ "}"
      f (FixT var ty1) = do
        ty1' <- local ((:) var) (f ty1)
        pure $ "Mu. " ++ var ++ " = " ++ ty1'
      f (VarT i) = ask >>= \ctx -> pure $ ctx !! i
      f (VariantT tys) = do
        tys' <- (traverse . traverse) f tys
        let g (tag, ty') = if ty' == "Unit" then tag else ty'
        pure . unwords . intersperse "|" $ g <$> tys'


prettyVariant :: [(Tag, Type)] -> Reader Bindings String
prettyVariant tys = pure . unwords . intersperse "|" $ f <$> tys
  where
    f :: (Varname, Type) -> String
    f (var, UnitT) = var
    f (var, ty) = var ++ " " ++ pretty ty
        --t1' <- local (const (x:ctx)) (f t1)

-- TODO: Replace this with a more robust pretty printer
instance Pretty Term where
  pretty t = runReader (f t) []
    where
      f :: Term -> Reader Bindings String
      f (App t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        pure $ "(" ++ t1' ++ " " ++ t2' ++ ")"
      f (Var x) = ask >>= \ctx -> pure $ ctx !! x
      f (Abs x ty t1) = do
        ctx <- ask
        t1' <- local (const (x:ctx)) (f t1)
        pure $ "(λ " ++ x ++ " : " ++ pretty ty ++ ". " ++ t1' ++ ")"
      f Tru = pure "True"
      f Fls = pure "False"
      f Unit = pure "Unit"
      f (As (Var i) ty) = do
        ctx <- ask
        let var = ctx !! i
        pure $ "(" ++ var ++ " as " ++ pretty ty ++ ")"
      f (As t1 ty) = f t1 >>= \t1' -> pure $ "(" ++ t1' ++ "as" ++ pretty ty ++ ")"
      f Z = pure "0"
      f s@(S _) = pure $ showNat s
      f (If t1 t2 t3) = do
        t1' <- f t1
        t2' <- f t2
        t3' <- f t3
        pure $ "If " ++ t1' ++ " then " ++ t2' ++ " else " ++ t3'
      f (Case l m v n) = do
        ctx <- ask
        l' <- f l
        m' <- f m
        n' <- local (const (v:ctx)) (f n)
        pure $ "case "   ++ l' ++ " of " ++
               "Z => " ++ m' ++ " | "  ++
               "S "    ++ v  ++ " => " ++ n'
      f (Let x t1 t2) = do
        ctx <- ask
        t1' <- f t1
        t2' <- local (const (x:ctx)) (f t2)
        pure $ "let " ++ x ++ " = " ++ t1' ++ " in " ++ t2'
      f (Pair t1 t2) = do
        t1' <- f t1
        t2' <- f t2
        pure $ "<" ++ t1' ++ ", " ++ t2' ++ ">"
      f (Fst t1) = (++ "fst ") <$> f t1
      f (Snd t1) = (++ "snd ") <$> f t1
      f (Tuple ts) = do
        ts' <- traverse (f . snd) ts
        pure $ "(" ++ commas ts' ++ ")"
      f (Get t1 v) = do
        t1' <- f t1
        pure $ "Get " ++ v ++ " from " ++ pretty t1'
      f (Record ts) = do
        ts' <- traverse (\(v1,t1) -> (++) (v1 ++ "=") <$> f t1) ts
        pure $ "{" ++ commas ts' ++ "}"
      f (Tag tag Unit) = pure tag
      f (Tag tag t1) = pure $ tag ++ " " ++ pretty t1
      f (VariantCase t1 cases) = do
        ctx <- ask
        t1' <- f t1
        let cases' = filter (\(tag,_, _) -> tag `notElem` ctx) cases
        patterns <- traverse (\(tag, bndr, t') -> do
          tC <- local (const (tag:ctx)) (f t')
          let bndr' = maybe mempty ( (:) ' ' . pretty) bndr
          pure $ tag ++ bndr' ++ " => " ++ tC
          ) cases'
        pure $ "variantCase "  ++ t1' ++ " of " ++ show (pretty <$> patterns)
      -- TODO: Consider and define a more appropriate pretty printer:
      f (FixLet t1) = f t1
      f (Roll _ t1) = pure $ pretty t1
      f (Unroll _ t1) = pure $ pretty t1

