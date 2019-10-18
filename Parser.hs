module TypedLambdaCalcInitial.Parser where

import Control.Applicative hiding (some)
import Control.Monad.Reader

import Data.Functor.Identity
import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import TypedLambdaCalcInitial.Types

infixr 4 <$$>
(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) = fmap . fmap

type Env = [(Varname, Int)]

type Parser a = ParsecT Void String (Reader Env) a

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

parserVar :: Parser Term
parserVar = do
  env <- ask
  val <- some letterChar
  return $ maybe (Var 0) Var (lookup val env)

updateEnv :: Varname -> Env -> Env
updateEnv var env = (var, 0):((+1) <$$> env)

parseBool :: Parser Type
parseBool = symbol "Bool" *> pure Boo

parseArrow :: Parser Type
parseArrow = do
  a <- parseBool <|> parens parseArrow
  sc
  symbol "->" *> pure ()
  sc
  b <- parseBool <|> parens parseArrow
  return (Func a b)

parseTypeSig :: Parser Type
parseTypeSig = try parseArrow <|> parseBool

parserAbs :: Parser Term
parserAbs = do
  env <- ask
  symbol "\\"
  sc
  var <- some letterChar
  sc
  symbol ":"
  sc
  ty <- parseTypeSig
  symbol "."
  sc
  term <- local (updateEnv var) parserTerm
  return (Abs var ty term)

parserTerm :: Parser Term
parserTerm = foldl1 App <$> (parserAbs <|> parserVar <|> parens parserTerm) `sepBy1` sc

runParse :: String -> Either (ParseErrorBundle String Void) Term
runParse = runIdentity . flip runReaderT [] . runParserT parserTerm mempty

run p = runIdentity . flip runReaderT [] . runParserT p mempty
