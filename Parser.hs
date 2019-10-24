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

parserNat :: Parser Term
parserNat = do
   digits <- read <$> some digitChar :: Parser Int
   return . foldr (\a b -> a b) Z $ replicate digits S

parserBools :: Parser Term
parserBools = parserFls <|> parserTru

updateEnv :: Varname -> Bindings -> Bindings
updateEnv var env = Snoc env var

parserNatT :: Parser Type
parserNatT = symbol "Nat" *> pure NatT

parserBoolT :: Parser Type
parserBoolT = symbol "Bool" *> pure BoolT

parserArrowT :: Parser Type
parserArrowT = do
  a <- parserNatT <|> parserBoolT <|> parens parserArrowT
  sc
  symbol "->" *> pure ()
  sc
  b <- parserNatT <|> parserBoolT <|> parens parserArrowT
  return (FuncT a b)

parseType :: Parser Type
parseType = try parserArrowT <|> parserBoolT <|> parserNatT

parserAbs :: Parser Term
parserAbs = do
  void $ symbol "\\"
  sc
  var <- some letterChar
  sc
  void $ symbol ":"
  sc
  ty <- parseType
  void $ symbol "."
  sc
  term <- local (updateEnv var) parserTerm
  return (Abs var ty term)

parserTerm :: Parser Term
parserTerm = foldl1 App <$> (  parserAbs
                           <|> parserBools
                           <|> parserNat
                           <|> parserVar
                           <|> parens parserTerm
                            ) `sepBy1` sc

handleParseErr :: Either ParseErr Term -> Either Err Term
handleParseErr val = either (Left . P) Right val

runParse :: String -> Either Err Term
runParse = handleParseErr . runIdentity . flip runReaderT Nil . runParserT parserTerm mempty

run :: ParsecT e s (ReaderT (SnocList a1) Identity) a2 -> s -> Either (ParseErrorBundle s e) a2
run p = runIdentity . flip runReaderT Nil . runParserT p mempty

