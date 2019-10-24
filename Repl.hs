{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE KindSignatures #-}
--module TypedLambdaCalcInitial.Repl (repl) where
module TypedLambdaCalcInitial.Repl where

import Control.Exception (Exception)
import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except

import Data.Void

import Text.Megaparsec.Error

import qualified System.Console.Haskeline as H
import System.Console.Haskeline.MonadException

import TypedLambdaCalcInitial.Types
import TypedLambdaCalcInitial.Parser
import TypedLambdaCalcInitial.Interpreters


-------------
--- ReplT ---
-------------

type Repl = ReplT IO
newtype ReplT (m :: * -> *) a = ReplT { unRepl :: H.InputT m a }
    deriving (Monad, Functor, Applicative, MonadIO, MonadException, MonadTrans, MonadRepl)

runReplT :: MonadException m =>  ReplT m a -> m a
runReplT m = H.runInputT H.defaultSettings (H.withInterrupt (unRepl m))

runRepl :: Repl a -> IO a
runRepl = runReplT

instance MonadException m => MonadException (ExceptT e m) where
    controlIO f = ExceptT $ controlIO $ \(RunIO run) -> let
        run' = RunIO (fmap ExceptT . run . runExceptT)
        in runExceptT <$> f run'

class MonadException m => MonadRepl m where
    getInputLine :: String -> m (Maybe String)
    getInputChar :: String -> m (Maybe Char)
    outputStr    :: String -> m ()
    outputStrLn  :: String -> m ()

instance MonadException m => MonadRepl (H.InputT m) where
    getInputLine = H.getInputLine
    getInputChar = H.getInputChar
    outputStr = H.outputStr
    outputStrLn = H.outputStrLn

instance MonadRepl m => MonadRepl (ExceptT e m) where
    getInputLine = lift . getInputLine
    getInputChar = lift . getInputChar
    outputStr = lift . outputStr
    outputStrLn = lift . outputStrLn

class ShowE e where
  showE :: e -> String

instance ShowE () where
  showE = show

instance ShowE Err where
  showE (T err) = show err
  showE (P err) = show err

instance ShowE TypeErr where
  showE = show

instance ShowE ParseErr where
  showE = errorBundlePretty

abort :: (MonadRepl m) => m a
abort = throwIO H.Interrupt

hoistError :: (MonadRepl m, ShowE e, MonadError e m) => Either e a -> m a
hoistError (Left err) = outputStrLn (showE err) >> throwIO ReplInterrupt
hoistError (Right a) = return a

data ReplInterrupt = ReplInterrupt
  deriving Show

instance Exception ReplInterrupt

handleReplInterrupt :: MonadRepl m => ReplInterrupt -> m ()
handleReplInterrupt _ = pure ()

repl :: IO ()
repl = runRepl loop
  where loop :: MonadRepl m => m ()
        loop = do
          str <- getInputLine "> "
          case str of
            Nothing -> abort
            Just str' -> do
              let res = do
                    parsed  <- runParse str'
                    checked <- runTypecheckM Nil (typecheck parsed)
                    reduced <- (Right $ multiStepEval Nil parsed :: Either Err Term)
                    return $ pretty reduced
              either (outputStrLn . showE) outputStrLn res
              loop
{-
data LC a
   = Var' a
   | App' (LC a) (LC a)
   | Abs' (LC (Maybe a))
   deriving (Functor, Foldable, Traversable)

instance Applicative LC where
  pure = Var'
  (<*>) = ap

instance Monad LC where
  Var' a >>= f = f a
  App' l r >>= f = App' (l >>= f) (r >>= f)
  Abs' k >>= f = Abs' $ k >>= \case
    Nothing -> pure Nothing
    Just a -> Just <$> f a

lam :: Eq a => a -> LC a -> LC a
lam v b = Abs' $ bind v <$> b where
  bind v u = u <$ guard (u /= v)
-}
