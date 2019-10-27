module TypedLambdaCalcInitial.Parser where

import Control.Applicative hiding (some, many)
import Control.Monad.Reader

import Data.Functor.Identity
import Data.List

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import TypedLambdaCalcInitial.Types

-- TODO: look into deriving MonadParsec
-- newtype Parser a = Parser { runParser :: ParsecT Void String (Reader Bindings) a }
--   deriving MonadParsec
type Parser a = ParsecT UnboundError String (Reader Bindings) a


handleParseErr :: Either ParseErr Term -> Either Err Term
handleParseErr val = either (Left . P) Right val

runParse :: String -> Either Err Term
runParse = handleParseErr . runIdentity . flip runReaderT [] . runParserT pTerm mempty

run :: Parser a -> String -> Either ParseErr a
run p = runIdentity . flip runReaderT [] . runParserT p mempty


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
rws = [ "if"
      , "then"
      , "else"
      , "True"
      , "False"
      , "case"
      , "of"
      , "Z"
      , "S"
      , "|"
      , "Unit"
      , "as"
      , "let"
      , "in"
      , "="
      ]

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

pUnitT :: Parser Type
pUnitT = rword "Unit" *> pure UnitT

pNatT :: Parser Type
pNatT = rword "Nat" *> pure NatT

pBoolT :: Parser Type
pBoolT = rword "Bool" *> pure BoolT

pArrowNest :: Parser Type
pArrowNest = parens pArrow

pArrow :: Parser Type
pArrow = do
  types <- (parens pArrow <|> pNatT <|> pBoolT <|> pUnitT) `sepBy1` arrow
  pure $ foldr1 FuncT types

parseType :: Parser Type
parseType = try pArrow <|> pBoolT <|> pNatT


-- | Terms:

pUnit :: Parser Term
pUnit = rword "Unit" *> pure Unit

pBool :: Parser Term
pBool = (rword "True" *> pure Tru) <|> (rword "False" *> pure Fls)

searchContext :: Eq a => [a] -> a -> Maybe Int
searchContext ctx val = (find (== val) ctx) >>= flip elemIndex ctx

pVar :: Parser Term
pVar = do
  ctx <- ask
  val <- identifier
  if null ctx
    then pure $ Var 0
    else case searchContext ctx val of
           Just i -> pure $ Var i
           Nothing -> customFailure $ UnboundError $ val ++ " not in scope."

pIf :: Parser Term
pIf = do
  rword "if" *> colon
  t1 <- pTerm
  rword "then" *> colon
  t2 <- pTerm
  rword "else" *> colon
  t3 <- pTerm
  pure $ If t1 t2 t3

pPeano :: Parser Term
pPeano =
  rword "S" *> (S <$> pTerm) <|> (rword "Z" *> pure Z)

pNat :: Parser Term
pNat = do
   digits <- fromIntegral <$> integer
   pure . foldr (\a b -> a b) Z $ replicate digits S

pAs :: Parser Term
pAs = try $ do
  t1 <- pValues
  rword "as"
  ty <- parseType
  pure $ As t1 ty

pCase :: Parser Term
pCase = do
  rword "case"
  l <- pTerm
  rword "of"
  rword "Z"
  phatArrow
  m <- pTerm
  pipe
  x <- parensOpt $ rword "S" *> identifier
  phatArrow
  n <- pTerm
  pure $ Case l m x n

pLet :: Parser Term
pLet = do
  rword "let"
  var <- identifier
  rword "="
  t1 <- pTerm
  rword "in"
  t2 <- local (updateEnv var) pTerm
  pure $ Let var t1 t2

updateEnv :: Varname -> Bindings -> Bindings
updateEnv var env = var : env

pAbs :: Parser Term
pAbs = do
  void $ symbol "\\"
  var <- identifier
  colon
  ty <- parseType
  dot
  term <- local (updateEnv var) pTerm
  pure (Abs var ty term)

pValues :: Parser Term
pValues = pUnit <|> pBool <|> pNat <|> pPeano <|> pVar

pStmts :: Parser Term
pStmts = pCase <|> pAbs <|> pLet <|> pAs

-- TODO: Fix parser bug when an extra close paren is present:
-- > ((\x:Bool.True) True)) True
-- True
pTerm :: Parser Term
pTerm = foldl1 App <$> (  pIf
                           <|> pStmts
                           <|> pValues
                           <|> parens pTerm
                            ) `sepBy1` sc

