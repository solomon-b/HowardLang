module HowardLang.Parser.Combinators where

import Control.Monad.Reader
import Data.Functor.Identity
import Text.Megaparsec

import HowardLang.Types (UnboundError, ParseErr, Term, Varname, Err(..), Bindings)

type Parser a = ParsecT UnboundError String (Reader Bindings) a

handleParseErr :: Either ParseErr Term -> Either Err Term
handleParseErr = either (Left . P) Right

runParse :: Parser Term -> String -> Either Err Term
runParse p = handleParseErr . runIdentity . flip runReaderT [] . runParserT p mempty

-- Updates DeBruijn index beindings during bindings
updateEnv :: Varname -> Bindings -> Bindings
updateEnv var env = var : env

bindLocalVar :: Varname -> Parser a -> Parser a
bindLocalVar var = local (updateEnv var)

-- Used for debugging combinators:
run :: Parser a -> String -> Either ParseErr a
run p = runIdentity . flip runReaderT [] . runParserT p mempty
