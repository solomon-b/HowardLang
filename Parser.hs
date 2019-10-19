module TypedLambdaCalcInitial.Parser where

import Control.Applicative hiding (some)
import Control.Monad.Reader

import Data.Functor.Identity
import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import TypedLambdaCalcInitial.Types

type Parser a = ParsecT Void String (Reader Context) a

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
  return $ maybe (Var 0) Var (getIndexFromContext env val)

parserTru :: Parser Term
parserTru = symbol "True" >> pure Tru

parserFls :: Parser Term
parserFls = symbol "False" >> pure Fls

parserBools :: Parser Term
parserBools = parserFls <|> parserTru

updateEnv :: Varname -> Context -> Context
updateEnv var env = Snoc env (var, NameBind)

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
parserTerm = foldl1 App <$> (  parserAbs
                           <|> parserBools
                           <|> parserVar
                           <|> parens parserTerm
                            ) `sepBy1` sc

runParse :: String -> Either (ParseErrorBundle String Void) Term
runParse = runIdentity . flip runReaderT Nil . runParserT parserTerm mempty

run p = runIdentity . flip runReaderT Nil . runParserT p mempty




execReaderT :: Monad m => ReaderT r m a -> r -> m r
execReaderT rma env = runReaderT (rma >> ask) env

execParse :: String -> Context
execParse = runIdentity . flip execReaderT Nil . runParserT parserTerm mempty

