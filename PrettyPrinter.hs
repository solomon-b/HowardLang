module TypedLambdaCalcInitial.PrettyPrinter where

import Control.Monad.Reader
--import qualified Data.Text.Prettyprint.Doc as P

import TypedLambdaCalcInitial.Types

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
    f _ = undefined

-- TODO: Replace this with a more robust pretty printer
pretty :: Term -> String
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
      pure $ "(λ " ++ x ++ " : " ++ show ty ++ ". " ++ t1' ++ ")"
    f Tru = pure "True"
    f Fls = pure "False"
    f Unit = pure "Unit"
    f (As (Var i) ty) = do
      ctx <- ask
      let var = ctx !! i
      pure $ "(" ++ var ++ " as " ++ show ty ++ ")"
    f (As t1 ty) = f t1 >>= \t1' -> pure $ "(" ++ t1' ++ "as" ++ show ty ++ ")"
    f Z = pure "0"
    f s@(S _) = pure $ show s
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
      pure $ "case "   ++ l' ++ " of: " ++
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
      pure $ "{" ++ t1' ++ ", " ++ t2' ++ "}"
    f (Fst t1) = (++ "fst ") <$> f t1
    f (Snd t1) = (++ "snd ") <$> f t1
