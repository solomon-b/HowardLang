module TypedLambdaCalcInitial.Parser where

import Control.Applicative hiding (some, many)
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


handleParseErr :: Either ParseErr Term -> Either Err Term
handleParseErr val = either (Left . P) Right val

runParse :: String -> Either Err Term
runParse = handleParseErr . runIdentity . flip runReaderT Nil . runParserT parserTerm mempty

run :: Parser a -> String -> Either ParseErr a
run p = runIdentity . flip runReaderT Nil . runParserT p mempty


-------------
--- Lexer ---
-------------

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens p = between (symbol "(") (symbol ")") p

parensOpt :: Parser a -> Parser a
parensOpt p = parens p <|> p

integer :: Parser Integer
integer = lexeme L.decimal

semi :: Parser ()
semi = void $ symbol ";"

colon :: Parser ()
colon = void $ symbol ":"

dot :: Parser ()
dot = void $ symbol "."

arrow :: Parser ()
arrow = void $ symbol "->"

phatArrow :: Parser ()
phatArrow = void $ symbol "=>"

pipe :: Parser ()
pipe = void $ symbol "|"

rword :: String -> Parser ()
rword w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

rws :: [String]
rws = ["if", "then", "else", "True", "False", "case", "of", "Z", "S", "|", "Unit"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p :: Parser String
    p = (:) <$> letterChar <*> many alphaNumChar
    check :: String -> Parser String
    check str = if str `elem` rws
                 then fail $ "keyword " ++ show str ++ " cannot be an identifier"
                 else pure str


--------------
--- Parser ---
--------------

-- | Types

parserUnitT :: Parser Type
parserUnitT = rword "Unit" *> pure UnitT

parserNatT :: Parser Type
parserNatT = rword "Nat" *> pure NatT

parserBoolT :: Parser Type
parserBoolT = rword "Bool" *> pure BoolT

parserArrowNest :: Parser Type
parserArrowNest = parens parserArrow

parserArrow :: Parser Type
parserArrow = do
  types <- (parens parserArrow <|> parserNatT <|> parserBoolT <|> parserUnitT) `sepBy1` arrow
  pure $ foldr1 FuncT types

parseType :: Parser Type
parseType = try parserArrow <|> parserBoolT <|> parserNatT


-- | Terms:

parserUnit :: Parser Term
parserUnit = rword "Unit" *> pure Unit

parserBool :: Parser Term
parserBool = (rword "True" *> pure Tru) <|> (rword "False" *> pure Fls)

parserVar :: Parser Term
parserVar = do
  env <- ask
  val <- identifier
  pure $ maybe (Var 0) Var $ (find (== val) env) >>= snocIndex env

parserIf :: Parser Term
parserIf = do
  rword "if" *> colon
  t1 <- parserTerm
  rword "then" *> colon
  t2 <- parserTerm
  rword "else" *> colon
  t3 <- parserTerm
  pure $ If t1 t2 t3

parserPeano :: Parser Term
parserPeano =
  rword "S" *> (S <$> parserTerm) <|> (rword "Z" *> pure Z)

parserNat :: Parser Term
parserNat = do
   digits <- fromIntegral <$> integer
   pure . foldr (\a b -> a b) Z $ replicate digits S

parserCase :: Parser Term
parserCase = do
  rword "case"
  l <- parserTerm
  rword "of"
  rword "Z"
  phatArrow
  m <- parserTerm
  pipe
  x <- parensOpt $ rword "S" *> identifier
  phatArrow
  n <- parserTerm
  pure $ Case l m x n


updateEnv :: Varname -> Bindings -> Bindings
updateEnv var env = Snoc env var

parserAbs :: Parser Term
parserAbs = do
  void $ symbol "\\"
  var <- identifier
  colon
  ty <- parseType
  dot
  term <- local (updateEnv var) parserTerm
  pure (Abs var ty term)

-- TODO: Fix parser bug when an extra close paren is present:
-- > ((\x:Bool.True) True)) True
-- True
parserTerm :: Parser Term
parserTerm = foldl1 App <$> (  parserIf
                           <|> parserCase
                           <|> parserAbs
                           <|> parserUnit
                           <|> parserBool
                           <|> parserNat
                           <|> parserPeano
                           <|> parserVar
                           <|> parens parserTerm
                            ) `sepBy1` sc

