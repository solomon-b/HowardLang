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

import Control.Monad.Except
import Data.List
import Text.Megaparsec.Error

import System.Console.Repline
import System.Exit

import TypedLambdaCalcInitial.Types
import TypedLambdaCalcInitial.Parser
import TypedLambdaCalcInitial.Interpreters

------------
--- Main ---
------------

type Repl a = HaskelineT IO a

repl :: IO ()
repl = evalRepl (pure "λ> ") cmd options (Just ':') (Word completer) (pure ())


----------------------
--- Error Handling ---
----------------------

class ShowE e where
  showE :: e -> String

instance ShowE () where
  showE = show

instance ShowE Err where
  showE (T err) = showE err
  showE (P err) = showE err

instance ShowE TypeErr where
  showE = show

instance ShowE ParseErr where
  showE = errorBundlePretty

hoistErr :: ShowE e => Either e a -> Repl a
hoistErr (Right val) = return val
hoistErr (Left err) = do
  liftIO $ putStrLn $ showE err
  abort

----------------
--- Commands ---
----------------

options :: [(String, [String] -> Repl ())]
options = [
    ("help", help)
  , ("h", help)
  , ("quit", quit)
  , ("q", quit)
  , ("type", typeof)
  , ("t", typeof)

  ]

cmd :: String -> Repl ()
cmd input =
  let res = do
        parsed  <- runParse input
        _ <- runTypecheckM [] (typecheck parsed)
        reduced <- (Right $ multiStepEval [] parsed :: Either Err Term)
        return $ pretty reduced
  in liftIO $ either (putStrLn . showE) putStrLn res

quit :: a -> Repl ()
quit _ = liftIO $ exitSuccess

typeof :: [String] -> Repl ()
typeof strs = do
  term <- hoistErr . runParse $ unwords strs
  ty <- hoistErr $ runTypecheckM [] (typecheck term)
  liftIO $ print ty

help :: a -> Repl ()
help _ = liftIO $ do
  putStrLn "Top Level Commands:"
  putStrLn ":quit                       Quits"
  putStrLn ":help                       Prints this message"
  putStrLn ":type <expr>                Checks the type of an expression"

-- TODO: Implement stateful completer or not?
completer :: Monad m => WordCompleter m
completer n = do
  let names = []
  return $ filter (isPrefixOf n) names
