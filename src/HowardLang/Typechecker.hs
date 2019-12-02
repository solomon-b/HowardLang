{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module HowardLang.Typechecker where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader

import Data.Functor.Foldable
import Data.Maybe (mapMaybe)
import Control.Monad.State

import Lens.Micro
import Lens.Micro.TH

import HowardLang.Types
import HowardLang.PrettyPrinter


newtype TypecheckT m a =
  TypecheckT { unTypecheckT :: ExceptT Err (ReaderT Context m) a }
  deriving (Functor, Applicative, Monad, MonadReader Context, MonadError Err)

type TypecheckM a = TypecheckT Identity a

runTypecheckT :: Context -> TypecheckT m a -> m (Either Err a)
runTypecheckT gamma = flip runReaderT gamma . runExceptT . unTypecheckT

runTypecheckM :: Context -> TypecheckT Identity a -> Either Err a
runTypecheckM gamma = runIdentity . runTypecheckT gamma

typetest :: Term -> Either Err Type
typetest = runTypecheckM [] . typecheck

-- TODO: Make this safer
getBinding :: Context -> Int -> Type
getBinding xs i = snd $ xs !! i

-- TODO: Improve error reporting!!!!
natToInt :: MonadError Err m => Term -> m Int
natToInt Z = pure 0
natToInt (S t) = (+1) <$> natToInt t
natToInt _ = throwTypeError' "Type Error: Excepted Nat"

checkTotal :: MonadError Err m => [a] -> [b] -> m ()
checkTotal xs ys = if length xs /= length ys then throwTypeError' "Error: Pattern Match Non-Total" else pure ()

-- TODO: How would I write this as a recursion scheme?
infixl !!!
(!!!) :: [a] -> Int -> Maybe a
(!!!) [] _ = Nothing
(!!!) (x:_) 0 = Just x
(!!!) (_:xs) i = xs !!! (i - 1)

typecheck :: (MonadError Err m , MonadReader Context m) => Term -> m Type
typecheck = para ralgebra
  where
    ralgebra :: (MonadError Err m , MonadReader Context m) => TermF (Term, m Type) -> m Type
    ralgebra = \case
      VarF i -> asks (`getBinding` i)
      AppF (t1, mty1) (_, mty2) -> mty1 >>= \case
        FuncT ty1 ty2 -> do
          ty2' <- mty2
          if ty2' == ty1
            then pure ty2
            else throwTypeError t1 ty1 ty2'
        ty -> throwTypeError' $ pretty t1 ++ " :: " ++ show ty ++ " is not a function"
      AbsF var ty (_, mty2) -> FuncT ty <$> local (update var ty) mty2
      LetF v (_, mty1) (_, mty2) -> mty1 >>= \ty1 -> local (update v ty1) mty2
      CaseF (n, mnTy) (z, mzTy) v (_, msTy) -> mnTy >>= \case
        NatT -> do
          zTy <- mzTy
          sTy <- local (update v NatT ) msTy
          if zTy == sTy
            then pure sTy
            else throwTypeError z zTy sTy
        nTy -> throwTypeError n nTy NatT
      VariantCaseF (_, mty1) cases -> mty1 >>= \case
        VariantT casesT -> do
          let cases' = mapMaybe (traverseOf _2 id) cases
          checkTotal cases casesT
          types <- traverse (bindLocalTags' casesT) cases'
          if allEqual types
            then pure $ head types
            else throwTypeError' $ "Type mismatch between cases: " ++ show types
        ty -> throwTypeError' $ "Expected a Variant Type but got: " ++ show ty
      UnitF -> pure UnitT
      TruF -> pure BoolT
      FlsF -> pure BoolT
      ZF -> pure NatT
      IfF (t1, mty1) (t2, mty2) (_, mty3) -> mty1 >>= \case
        BoolT -> mty2 >>= \ty2 -> mty3 >>= \ty3 -> if ty2 == ty3 then pure ty2 else throwTypeError t2 ty2 ty3
        ty1 -> throwTypeError t1 ty1 BoolT
      SF (t1, mty) -> mty >>= \case
        NatT -> pure NatT
        ty -> throwTypeError t1 ty NatT
      AsF (t@(Tag tag _), mtagTy) ty -> mtagTy >>= \ty1 ->
        case ty of
          VariantT tys ->
            case lookup tag tys of
              Just ty' | ty' == ty1 -> pure ty
              _ -> throwTypeError t ty1 ty -- TODO: Improve this error, it does not reference the sum type.
          _ -> throwTypeError t ty1 ty
      AsF (t1, mTy) ty -> mTy >>= \ty1' ->
        if ty1' == ty
           then pure ty
           else throwTypeError t1 ty1' ty
      TupleF ts -> TupleT . fmap snd <$> traverse (traverse snd) ts
      GetF (_, mTys) tag -> mTys >>= \case
        TupleT tys -> maybe (throwTypeError' "Type Error: Projection failed") pure (tys !!! read tag)
        RecordT tys -> maybe (throwTypeError' "Type Error: Projection failed") pure (lookup tag tys)
        _ -> throwTypeError' "Catastrophic failure! This shouldnt be possible."
      FixLetF (t1, mTy) -> mTy >>= \case
        FuncT ty1 ty2 | ty1 == ty2 -> pure ty2
        FuncT ty1 ty2 -> throwTypeError t1 ty2 ty1
        ty -> throwTypeError' $ "Type Error: " ++ show ty ++ " is not a function type"
      UnrollF u (_, mTy1) ->
        case u of
          FixT _ ty -> do
            let u' = typeSubstTop u ty
            ty1 <- mTy1
            if ty1 == u
              then pure u'
              else throwTypeError' "Type Error: Temp Error bad Unroll"
          _ -> mTy1
      RollF u (_, mTy1) ->
        case u of
          FixT _ ty -> do
            let u' = typeSubstTop u ty
            ty1 <- mTy1
            if ty1 == u'
              then pure u
              else throwTypeError' $ "Type Error: " ++ show u' ++ " != " ++ show ty1
          _ -> mTy1
      FstF (t, mTy) ->
        case t of
          Pair{} -> mTy
          _ -> mTy >>= \case
            PairT ty1 _ -> pure ty1
            ty -> throwTypeError' $ "Expected a Pair but got: " ++ show ty
      SndF (t, mTy) ->
        case t of
          Pair{} -> mTy
          _ -> mTy >>= \case
            PairT _ ty2 -> pure ty2
            ty -> throwTypeError' $ "Expected a Pair but got: " ++ show ty
      PairF (_, mTy1) (_, mTy2) -> PairT <$> mTy1 <*> mTy2
      RecordF ts -> RecordT <$> traverse (traverse snd) ts
      TagF _ (_, mTy) -> mTy

    update :: Varname -> Type -> Context -> Context
    update var ty = (:) (var, ty)
    bindLocalTags' ty1 (tag, bndr, (_, mTy)) = case lookup tag ty1 of
      Just tyC -> local (update bndr tyC) mTy
      Nothing -> throwTypeError' $ "Expected type: " ++ show (VariantT ty1)


-------------------------
--- Type Substitution ---
-------------------------

typeShift :: DeBruijn -> Type -> Type
typeShift target t = runReader (cataA algebra t) 0
  where
    algebra :: TypeF (Reader Int Type) -> Reader Int Type
    algebra = \case
      VarTF j    -> ask >>= \i -> if j >= i then pure (VarT $ j + target) else pure (VarT j)
      FixTF b t1 -> FixT b <$> local (+1) t1
      t'         -> fmap embed (sequenceA t')

typeSubst :: DeBruijn -> Type -> Type -> Type
typeSubst target s t = runReader (cataA algebra t) (s, 0)
  where
    algebra :: TypeF (Reader (Type, Int) Type) -> Reader (Type, Int) Type
    algebra = \case
      VarTF x    -> ask >>= \ctx -> if x == target + snd ctx then pure (fst ctx) else pure (VarT x)
      FixTF b ty -> FixT b <$> local update ty
      t'         -> fmap embed (sequenceA t')
    update :: (Type, Int) -> (Type, Int)
    update (ty, i) = (ty, i + 1)

typeSubstTop :: Type -> Type -> Type
typeSubstTop s t = typeShift (-1) (typeSubst 0 (typeShift 1 s) t)


------------------------------------------------------------
------ TODO: IMPROVE ERROR MESSAGING MASSIVELY !!!!!! ------
------------------------------------------------------------
{-
Does this form encapsulate all type errors?
"Type Error: Term {t} of type `{T1}` does not match expected type {T2} in expression: {TERM}."
-}

throwTypeError :: MonadError Err m => Term -> Type -> Type -> m a
throwTypeError t1 ty1 ty2 = throwError . T . TypeError $
  "Type Error:\n\r" ++
  "Expected Type: " ++ show ty2 ++ "\n\r" ++
  "Actual Type: "   ++ show ty1 ++ "\n\r" ++
  "For Term: "      ++ pretty t1

throwTypeError' :: MonadError Err m => String -> m a
throwTypeError' = throwError . T . TypeError


----------------------------
--- Constraint Generator ---
----------------------------


-- Blatently stolen from Chris Penner's Candor
genFresh :: [String]
genFresh = ((: []) <$> ['a'..'z']) ++
  do
    n <- [1..] :: [Int]
    a <- ['a'..'z']
    pure (a : show n)

type Constraint = (Type, Type)
data InferCtx  = InferCtx { _freshNames :: [String], _constraints :: [Constraint] }

makeLenses ''InferCtx

type InferM a = ReaderT Context (State InferCtx) a

evalInferM :: Context -> InferM a -> a
evalInferM gamma = flip evalState ctx . flip runReaderT gamma
  where
    ctx :: InferCtx
    ctx = InferCtx { _freshNames = genFresh, _constraints =  [] }

execInferM :: Context -> InferM a -> InferCtx
execInferM gamma = flip execState ctx . flip runReaderT gamma
  where
    ctx :: InferCtx
    ctx = InferCtx { _freshNames = genFresh, _constraints =  [] }

recon :: Term -> InferM Type
recon = \case
  Var i -> asks (`getBinding` i)
  Abs v ty term -> do
    ty2 <- local ((:) (v, ty)) (recon term)
    pure $ FuncT ty ty2
  App t1 t2 -> do
    ty1 <- recon t1
    ty2 <- recon t2
    names <- gets _freshNames
    cnstrs <- gets _constraints
    let freshName = head names
    put $ InferCtx (tail names) $ (ty1, FuncT ty2 (TVar freshName)):cnstrs
    pure $ FuncT ty2 (TVar freshName)
  Tru -> pure BoolT
  Fls -> pure BoolT
  Z -> pure NatT
  S t -> do
    ty <- recon t
    modify $ over constraints ((:) (ty, NatT))
    pure NatT
  If t1 t2 t3 -> do
    ty1 <- recon t1
    ty2 <- recon t2
    ty3 <- recon t3
    modify $ over constraints ([(ty1, BoolT), (ty2, ty3)] ++)
    pure ty3


