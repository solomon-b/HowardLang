module TypedLambdaCalcInitial.Parser where

import Control.Applicative hiding (some)
import Control.Monad.Reader

import Data.Functor.Identity
import Data.List
import Data.Void

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import TypedLambdaCalcInitial.Types

-- TODO: look into deriving MonadParsec
-- newtype Parser a = Parser { runParser :: ParsecT Void String (Reader Bindings) a }
--   deriving MonadParsec
type Parser a = ParsecT Void String (Reader Bindings) a


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
  return $ maybe (Var 0) Var $ (find (== val) env) >>= snocIndex env

parserTru :: Parser Term
parserTru = symbol "True" >> pure Tru

parserFls :: Parser Term
parserFls = symbol "False" >> pure Fls

parserBools :: Parser Term
parserBools = parserFls <|> parserTru

updateEnv :: Varname -> Bindings -> Bindings
updateEnv var env = Snoc env var

parseBool :: Parser Type
parseBool = symbol "Bool" *> pure BoolT

parseArrow :: Parser Type
parseArrow = do
  a <- parseBool <|> parens parseArrow
  sc
  symbol "->" *> pure ()
  sc
  b <- parseBool <|> parens parseArrow
  return (FuncT a b)

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

handleParseErr :: Either ParseErr Term -> Either Err Term
handleParseErr val = either (Left . P) Right val

runParse :: String -> Either Err Term
runParse = handleParseErr . runIdentity . flip runReaderT Nil . runParserT parserTerm mempty

run p = runIdentity . flip runReaderT Nil . runParserT p mempty

