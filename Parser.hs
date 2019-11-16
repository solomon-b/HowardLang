module TypedLambdaCalcInitial.Parser where

import Control.Applicative hiding (some, many)
import Control.Monad.Reader

import Data.Functor.Identity
import Data.Foldable
import Data.List

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import TypedLambdaCalcInitial.Types

-----------------------
----- BNF Grammer -----
-----------------------
{-
ALPHA = "A".."Z" | "a".."z";
DIGIT = "0".."9";
INTEGER = DIGIT {DIGIT};

VAR = ALPHA {ALPHA | INTEGER};
BOOL = "True" | "False";
S = "S" TERM;
Z = "Z" | "0";
APP = TERM TERM;
ABS = ("\\" | "λ") VAR ":" TYPE "." TERM;
CASE = "case" TERM "of" "Z" "=>" TERM "|" "(S" VAR ")" "=>" TERM;
IF = "if:" TERM "then:" TERM "else:" TERM;
PAIR = "<" TERM "," TERM ">";
FST = "fst" TERM;
SND = "snd" TERM;
TUPLE = "(" TERM { "," TERM } ")";
PROJ = "get" TERM "[" VAR "]";
RECORD = "{" VAR "=" TERM { "," VAR "=" TERM } "}";
GROUP = "(" TERM ")";
INR = "inr" TERM TYPE;
INL = "inl" TERM TYPE;
SUMCASE = "sumCase" TERM "of" "(" "inl" VAR ")" "=>" TERM "|" "(" "inr" VAR ")" "=>" TERM;
TAG = "tag" VAR TERM "as" TYPE;
VARIANTCASE = "variantCase" TERM "of" VAR VAR "=>" TERM { "|" VAR VAR "=>" TERM };
FIX = fix TERM
LET = "let" VAR {"(" VAR ":" "TYPE" ")"} "=" TERM "in" TERM
LETREC = "letrec" VAR "=" TERM "in" TERM

TYPE = "Unit" | "Bool" | "Nat" | TYPE "->" "TYPE" | TYPE "x" TYPE | "(" TYPE { "," TYPE } ")" | "{" TYPE { "," TYPE } "}" | Sum Type Type;
TERM = GROUP | VAR | S | Z | BOOL | APP | ABS | CASE | IF | PAIR | FST | SND | TUPLE | PROJ | RECORD | INR | INL | SUMCASE | FIX | LET | LETREC;
-}


--------------
---- Main ----
--------------

type Parser a = ParsecT UnboundError String (Reader Bindings) a

handleParseErr :: Either ParseErr Term -> Either Err Term
handleParseErr val = either (Left . P) Right val

runParse :: String -> Either Err Term
runParse = handleParseErr . runIdentity . flip runReaderT [] . runParserT pMain mempty

-- Updates DeBruijn index beindings during bindings
updateEnv :: Varname -> Bindings -> Bindings
updateEnv var env = var : env

bindLocalVar :: Varname -> Parser a -> Parser a
bindLocalVar var env = local (updateEnv var) env

-- Used for debugging combinators:
run :: Parser a -> String -> Either ParseErr a
run p = runIdentity . flip runReaderT [] . runParserT p mempty


-- | Composed Parser

-- TODO: Recurses infinitely: `(tag Right (1, True) as (Left Unit | Right (Nat, Bool)))`
-- TODO: Parser blows up with out of scope Vars
pValues :: Parser Term
pValues = pTuple <|> pRecord <|> pPair <|> pUnit <|> pBool <|> pNat <|> pPeano <|> pVar

pStmts :: Parser Term
pStmts = pLetRec <|> pFix <|> pGet <|> pVariantCase <|> pTag <|> pSumCase <|> pInR <|> pInL <|> pCase <|> pAbs <|> pLet <|> pAs <|> pFst <|> pSnd

pTerm :: Parser Term
pTerm = foldl1 App <$> (  pIf
                      <|> try pStmts
                      <|> try pValues
                      <|> parens pTerm
                       ) `sepBy1` sc
pMain :: Parser Term
pMain = pTerm <* eof


-----------------
----- Lexer -----
-----------------

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

quoted :: Parser a -> Parser a
quoted = between (symbol "\"") (symbol "\"")

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

bracket :: Parser a -> Parser a
bracket = between (symbol "{") (symbol "}")

squareBracket :: Parser a -> Parser a
squareBracket = between (symbol "[") (symbol "]")

angleBracket :: Parser a -> Parser a
angleBracket = between (symbol "<") (symbol ">")

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

lambda :: Parser ()
lambda = void $ symbol "λ" <|> symbol "\\"

equal :: Parser ()
equal = void $ symbol "="

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
      , "fst"
      , "snd"
      , "get"
      , ","
      , "inl"
      , "inr"
      , "Sum"
      , "sumCase"
      , "variantCase"
      , "fix"
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

constructor :: Parser String
constructor = (lexeme . try) (p >>= check)
  where
    p :: Parser String
    p = (:) <$> upperChar <*> many alphaNumChar
    check :: String -> Parser String
    check str = if str `elem` rws
                 then fail $ "keyword " ++ show str ++ " cannot be an identifier"
                 else pure str

------------------
----- Parser -----
------------------
-----------
-- Types --
-----------

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

pPairT :: Parser Type
pPairT = do
  ty1 <- parseType
  void $ symbol "X"
  ty2 <- parseType
  pure $ PairT ty1 ty2

pSumT :: Parser Type
pSumT = do
  rword "Sum"
  ty1 <- parseType
  ty2 <- parseType
  pure $ SumT ty1 ty2

pVariantT :: Parser Type
pVariantT = do
  tags <- p `sepBy1` pipe
  pure $ VariantT tags
  where
    p = do
      tag <- constructor
      ty <- parseType
      pure (tag, ty)

parseType :: Parser Type
parseType = try pArrow <|> pVariantT <|> pSumT <|> pPairT <|> pBoolT <|> pNatT


-----------
-- Terms --
-----------

-- | Values

-- TODO: Figure out how to adjust `pTerm` to allow for `rword "()"`
pUnit :: Parser Term
pUnit = rword "Unit" *> pure Unit

pBool :: Parser Term
pBool = (rword "True" *> pure Tru) <|> (rword "False" *> pure Fls)

pPeano :: Parser Term
pPeano = rword "S" *> (S <$> pTerm) <|> (rword "Z" *> pure Z)

pNat :: Parser Term
pNat = do
   digits <- fromIntegral <$> integer
   pure . foldr (\a b -> a b) Z $ replicate digits S

pString :: Parser String
pString = do
  void $ symbol "\""
  manyTill asciiChar (char '\"')

pVar :: Parser Term
pVar = do
  ctx <- ask
  val <- identifier
  if null ctx
    then pure $ Var 0
    else case searchContext ctx val of
           Just i -> pure $ Var i
           Nothing -> customFailure $ UnboundError $ val ++ " not in scope."
  where
    searchContext :: Eq a => [a] -> a -> Maybe Int
    searchContext ctx val = (find (== val) ctx) >>= flip elemIndex ctx

pTuple :: Parser Term
pTuple = parens $ do
  ts <- zip nats <$> pTerm `sepBy1` symbol ","
  if length ts == 1
  then pure $ snd $ head ts
  else pure $ Tuple ts
  where
    nats = show <$> ([1..] :: [Int])

pRecord :: Parser Term
pRecord = bracket $ do
  ts <- pClause `sepBy1` symbol ","
  pure $ Record ts
  where
    pClause :: Parser (Varname, Term)
    pClause = do
      v1 <- identifier
      equal
      t1 <- pTerm
      pure (v1, t1)

pAbs :: Parser Term
pAbs = do
  lambda
  var <- identifier
  colon
  ty <- parseType
  dot
  term <- bindLocalVar var pTerm
  pure (Abs var ty term)

-- | Statements

pIf :: Parser Term
pIf = do
  rword "if" *> colon
  t1 <- pTerm
  rword "then" *> colon
  t2 <- pTerm
  rword "else" *> colon
  t3 <- pTerm
  pure $ If t1 t2 t3

pPair :: Parser Term
pPair = angleBracket $ do
  t1 <- pTerm
  void $ symbol ","
  t2 <- pTerm
  pure $ Pair t1 t2

pAs :: Parser Term
pAs = parens $ do
  t1 <- pTerm
  rword "as"
  ty <- parseType
  pure $ As t1 ty

-- TODO: Detect recursive call to `var` in `t1`
pLet :: Parser Term
pLet = do
  rword "let"
  var <- identifier
  params <- optional pLetParams
  rword "="
  t1 <- genCurriedAbs params
  rword "in"
  t2 <- bindLocalVar var pTerm
  pure $ Let var t1 t2

pLetParams :: Parser [(Varname, Type)]
pLetParams = some . parens $ do
  var <- identifier
  colon
  ty <- parseType
  pure (var, ty)

genCurriedAbs :: Maybe [(Varname, Type)] -> Parser Term
genCurriedAbs Nothing = pTerm
genCurriedAbs (Just xs) = ask >>= \ctx ->
    let bindings = foldl (flip updateEnv) ctx $ fst <$> xs
    in foldr (\(var, ty) t -> Abs var ty <$> t) (local (const bindings) pTerm) xs

pFst :: Parser Term
pFst = do
  rword "fst"
  t <- pTerm
  pure $ Fst t

pSnd :: Parser Term
pSnd = do
  rword "snd"
  t <- pTerm
  pure $ Snd t


pInL :: Parser Term
pInL = do
  rword "inl"
  t1 <- pTerm
  colon
  ty <- parseType
  pure $ InL t1 ty

pInR :: Parser Term
pInR = do
  rword "inr"
  t1 <- pTerm
  colon
  ty <- parseType
  pure $ InR t1 ty

pSumCase :: Parser Term
pSumCase = do
  rword "sumCase"
  t1 <- pTerm
  rword "of"
  vL <- parensOpt $ rword "inl" *> identifier
  phatArrow
  tL <- bindLocalVar vL pTerm
  pipe
  vR <- parensOpt $ rword "inr" *> identifier
  phatArrow
  tR <- bindLocalVar vR pTerm
  pure $ SumCase t1 tL vL tR vR

-- TODO: Rewrite Case parser to work with both sums and nats
pCase :: Parser Term
pCase = do
  rword "case"
  n <- pTerm
  rword "of"
  rword "Z"
  phatArrow
  z <- pTerm
  pipe
  var <- parensOpt $ rword "S" *> identifier
  phatArrow
  s <- bindLocalVar var pTerm
  pure $ Case n z var s

pTag :: Parser Term
pTag = do
  rword "tag"
  tag <- constructor
  term <- pTerm
  rword "as"
  ty <- parensOpt $ parseType
  pure $ Tag tag term ty

pVariantCase :: Parser Term
pVariantCase = do
  rword "variantCase"
  t1 <- pTerm
  rword "of"
  pats <- pVariantPattern `sepBy1` pipe
  pure $ VariantCase t1 pats

pVariantPattern :: Parser (Tag, Binder, Term)
pVariantPattern = do
  tagVar <- constructor
  equal
  tagBinder <- identifier
  phatArrow
  t <- bindLocalVar tagBinder pTerm
  pure (tagVar, tagBinder, t)

pFix :: Parser Term
pFix = do
  rword "fix"
  t <- pTerm
  pure $ Fix t

pLetRec :: Parser Term
pLetRec = do
  rword "letrec"
  var <- identifier
  rword "="
  t1 <- Fix <$> pTerm
  rword "in"
  t2 <- bindLocalVar var pTerm
  pure $ Let var t1 t2

-- TODO: Figure out how to prevent infinite recursion if I remove the reserved word.
pGet :: Parser Term
pGet = do
  rword "get"
  t1 <- pTerm
  t2 <- squareBracket identifier
  pure $ Get t1 t2
