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
import TypedLambdaCalcInitial.Typechecker (typeSubstTop)

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


Example Expressions:

(\x:Nat.x) === Abs "x" NatT (Var 0)

Example Type Signatures:
Product Type:
(Nat, Bool) === (NatT, BoolT)

Variant Type:
(Left Bool | Right Nat) === VarantT [("Left", BoolT), ("Right, NatT")]

Enumerated Type:
(Nothing | Just Nat) === VariantT [("Nothing", UnitT), ("Just", NatT)]
(Red | Blue | Green) === VariantT [("Red", UnitT), ("Blue", UnitT), ("Green", UnitT)]

Recursive Type:
mu. List: (Nil | Cons a List a)

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

comma :: Parser ()
comma = void $ symbol ","

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
      , "mu"
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
    check str = do
      ctx <- ask
      if str `elem` ctx ++ rws
        then fail $ show str ++ " is already bound"
        else pure str

------------------
----- Parser -----
------------------
-----------
-- Types --
-----------
{-
SHINY NEW TYPE PARSER

TYPE = "(" TYPE ")" | START END
START = UNIT | NAT | BOOL | SUM
END = "X" TYPE | "->" TYPE | EPSILON

FIXT = "mu." VAR TYPE
RECORD = "{" TYPE { , TYPE } "}"
TUPLE = "( TYPE { , TYPE } ")"
VARIANT = VAR [TYPE] { | VAR [TYPE] }
SUM = "SUM" TYPE TYPE
UNIT = "Unit" | "()"
NAT = "Nat"
BOOL = "Bool"
-}

data Tok t = PairTok t | ArrowTok t | Epsilon

pUnitT :: Parser Type
pUnitT = (rword "Unit" <|> rword "()") *> pure UnitT

pNatT :: Parser Type
pNatT = rword "Nat" *> pure NatT

pBoolT :: Parser Type
pBoolT = rword "Bool" *> pure BoolT

-- TODO: Record Types Need to Capture Identifiers
pRecordT :: Parser Type
pRecordT = bracket $ do
  tys <- p `sepBy1` comma
  pure $ RecordT tys
  where
    p = do
      tag <- identifier
      ty <- parseType
      pure (tag, ty)

-- TODO: Figure out how to allow for tuples to use parens
pTupleT' :: Parser Type
pTupleT' = squareBracket $ do
  ty <- parseType
  comma
  tys <- parseType `sepBy1` comma
  pure $ TupleT (ty:tys)

pSumT' :: Parser Type
pSumT' = do
  rword "Sum"
  t1 <- parseType
  t2 <- parseType
  pure $ SumT t1 t2

pVariantT' :: Parser Type
pVariantT' = do
  tags <- p `sepBy1` pipe
  pure $ VariantT tags
  where
    p :: Parser (String, Type)
    p = do
      tag <- constructor
      ty <- optional parseType
      case ty of
        Nothing -> pure (tag, UnitT)
        Just ty' -> pure (tag, ty')

-- | Recursive Type signature
pFixT :: Parser Type
pFixT = do
  rword "mu"
  dot
  var <- constructor
  colon
  ty <- bindLocalVar var parseType
  pure $ typeSubstTop (FixT var ty) ty

pVarT :: Parser Type
pVarT = do
  ctx <- ask
  val <- identifier
  if null ctx
    then pure $ VarT 0
    else case searchContext ctx val of
           Just i -> pure $ VarT i
           Nothing -> customFailure $ UnboundError $ val ++ " not in scope."
  where
    searchContext :: Eq a => [a] -> a -> Maybe Int
    searchContext ctx val = (find (== val) ctx) >>= flip elemIndex ctx

parseType :: Parser Type
parseType = do
  t1 <- parens parseType <|> start
  mT2 <- end
  case mT2 of
    Epsilon -> pure t1
    PairTok t2 -> pure $ PairT t1 t2
    ArrowTok t2 -> pure $ FuncT t1 t2

start :: Parser Type
start = pFixT <|> pUnitT <|> pNatT <|> pBoolT <|> pSumT' <|> pVariantT' <|> pTupleT' <|> pRecordT <|> pVarT 

end :: Parser (Tok Type)
end = arrowEnd <|> pairEnd <|> pure Epsilon
  where
    arrowEnd = do
      arrow
      t <- parseType
      pure $ ArrowTok t
    pairEnd  = do
      void $ symbol "X"
      t <- parseType
      pure $ PairTok t

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
  ty <- parensOpt parseType
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
  t1 <- parseAbsWrappedTerm params
  rword "in"
  t2 <- bindLocalVar var pTerm
  pure $ Let var t1 t2

pLetParams :: Parser [(Varname, Type)]
pLetParams = some . parens $ do
  var <- identifier
  colon
  ty <- parseType
  pure (var, ty)

parseAbsWrappedTerm :: Maybe [(Varname, Type)] -> Parser Term
parseAbsWrappedTerm Nothing = pTerm
parseAbsWrappedTerm (Just xs) = ask >>= \ctx ->
    let bindings = foldl (flip updateEnv) ctx $ fst <$> xs
    in foldr (\(var, ty) t -> Abs var ty <$> t) (local (const bindings) pTerm) xs

-- TODO: Add sugar to add `rec` param automagically
pLetRec :: Parser Term
pLetRec = do
  rword "letrec"
  var <- identifier
  params <- optional pLetParams
  rword "="
  t1 <- parseAbsWrappedTerm params
  rword "in"
  t2 <- bindLocalVar var pTerm
  pure $ Let var (Fix t1) t2

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
  isEnum <- optional $ lookAhead (rword "as")
  case isEnum of
    Just _ -> do
      rword "as"
      ty <- parensOpt $ parseType
      pure $ Tag tag Unit ty
    Nothing -> do
      term <- pTerm
      rword "as"
      ty <- parensOpt $ parseType
      -- TODO: DETECT IF TY CONTAINS FIXT THEN ROLL DAT BOI UP
      pure $ Tag tag term ty

pVariantCase :: Parser Term
pVariantCase = do
  rword "variantCase"
  t1 <- pTerm
  rword "of"
  pats <- pVariantPattern `sepBy1` pipe
  pure $ VariantCase t1 pats

pVariantPattern :: Parser (Tag, Maybe Binder, Term)
pVariantPattern = do
  tagVar <- constructor
  isEnum <- optional phatArrow
  case isEnum of
    Just _ -> pTerm >>= \t -> pure (tagVar, Nothing, t)
    Nothing -> do
      equal
      tagBinder <- identifier
      phatArrow
      t <- bindLocalVar tagBinder pTerm
      pure (tagVar, Just tagBinder, t)

-- λ> (fix (\rec:Nat->Nat->Nat.\x:Nat.\y:Nat.case x of Z => y | (S z) => rec z (S y))) 2 2
-- S (S (S (S Z)))
pFix :: Parser Term
pFix = do
  rword "fix"
  t <- pTerm
  pure $ Fix t

-- TODO: Figure out how to prevent infinite recursion if I remove the reserved word.
pGet :: Parser Term
pGet = do
  rword "get"
  t1 <- pTerm
  t2 <- squareBracket identifier
  pure $ Get t1 t2
