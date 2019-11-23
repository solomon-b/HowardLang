module HowardLang.Parser.Expression where

import Control.Applicative hiding (some, many)
import Control.Monad.Reader

import Data.Functor
import Data.List

import Lens.Micro

import Text.Megaparsec
import Text.Megaparsec.Char

import HowardLang.Types
import HowardLang.Parser.Combinators
import HowardLang.Parser.Token
import HowardLang.Typechecker (typeSubstTop)

-----------------------
----- BNF Grammer -----
-----------------------

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

{-
CURRENT TERM PARSER PLUS OLD TYPE PARSER -- TODO: UPDATE THIS

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
                       ) `sepBy1` whitespace
pMain :: Parser Term
pMain = whitespace *> pTerm <* eof

-----------
-- Types --
-----------

data Tok t = PairTok t | ArrowTok t | Epsilon

pUnitT :: Parser Type
pUnitT = (rword "Unit" <|> rword "()") $> UnitT

pNatT :: Parser Type
pNatT = rword "Nat" $> NatT

pBoolT :: Parser Type
pBoolT = rword "Bool" $> BoolT

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
pTupleT :: Parser Type
pTupleT = squareBracket $ do
  ty <- parseType
  comma
  tys <- parseType `sepBy1` comma
  pure $ TupleT (ty:tys)

pSumT :: Parser Type
pSumT = do
  rword "Sum"
  t1 <- parseType
  SumT t1 <$> parseType

pVariantT :: Parser Type
pVariantT = do
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
  ctx <- asks _bindings
  val <- identifier
  if null ctx
    then pure $ VarT 0
    else case searchContext ctx val of
           Just i -> pure $ VarT i
           Nothing -> customFailure $ UnboundError $ val ++ " not in scope."
  where
    searchContext :: Eq a => [a] -> a -> Maybe Int
    searchContext ctx val = find (== val) ctx >>= flip elemIndex ctx

parseType :: Parser Type
parseType = do
  t1 <- parens parseType <|> start
  mT2 <- end
  case mT2 of
    Epsilon -> pure t1
    PairTok t2 -> pure $ PairT t1 t2
    ArrowTok t2 -> pure $ FuncT t1 t2

start :: Parser Type
start = pFixT <|> pUnitT <|> pNatT <|> pBoolT <|> pSumT <|> pVariantT <|> pTupleT <|> pRecordT <|> pVarT 

end :: Parser (Tok Type)
end = arrowEnd <|> pairEnd <|> pure Epsilon
  where
    arrowEnd = arrow *> (ArrowTok <$> parseType)
    pairEnd  = symbol "X" *> (PairTok <$> parseType)

-----------
-- Terms --
-----------

-- | Values

-- TODO: Figure out how to adjust `pTerm` to allow for `rword "()"`
pUnit :: Parser Term
pUnit = rword "Unit" $> Unit

pBool :: Parser Term
pBool = (rword "True" $> Tru) <|> (rword "False" $> Fls)

pPeano :: Parser Term
pPeano = rword "S" *> (S <$> pTerm) <|> (rword "Z" $> Z)

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
  ctx <- asks _bindings
  val <- identifier
  if null ctx
    then pure $ Var 0
    else case searchContext ctx val of
           Just i -> pure $ Var i
           Nothing -> customFailure $ UnboundError $ val ++ " not in scope."
  where
    searchContext :: Eq a => [a] -> a -> Maybe Int
    searchContext ctx val = find (== val) ctx >>= flip elemIndex ctx

pTuple :: Parser Term
pTuple = squareBracket $ do
  ts <- zip nats <$> pTerm `sepBy1` symbol ","
  if length ts == 1
  then pure $ snd $ head ts
  else pure $ Tuple ts
  where
    nats = show <$> ([0,1..] :: [Int])

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
pPair = angleBracket $ Pair <$> pTerm <* symbol "," <*> pTerm

pAs :: Parser Term
pAs = parens $ As <$> pTerm <* rword "as" <*> parseType

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
parseAbsWrappedTerm (Just xs) = do
  ctx <- ask
  let bindings' = foldl (flip bindVar) ctx $ fst <$> xs
  foldr (\(var, ty) t -> Abs var ty <$> t) (local (const bindings') pTerm) xs

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
pFst = rword "fst" *> (Fst <$> pTerm)

pSnd :: Parser Term
pSnd = rword "snd" *> (Snd <$> pTerm)

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
  t1 <- try variant <|> enum
  optType <- optional $ do
    rword "as"
    parseType
  case optType of
    Just ty ->
      case findRec ty of
        Just fixT -> pure $ Roll fixT t1
        Nothing -> pure $ As t1 ty
    Nothing -> pure t1
  where
    variant :: Parser Term
    variant = Tag <$> constructor <*> pTerm
    enum :: Parser Term
    enum = Tag <$> constructor <*> pure Unit

pTag' :: Parser Term
pTag' = do
  rword "tag"
  tag <- constructor
  isEnum <- optional $ lookAhead (rword "as")
  case isEnum of
    Just _ -> do
      rword "as"
      ty <- parensOpt parseType
      case findRec ty of
        Just fixT -> pure $ Roll fixT $ As (Tag tag Unit) ty
        Nothing -> pure $ As (Tag tag Unit) ty
    Nothing -> do
      term <- pTerm
      rword "as"
      ty <- parensOpt parseType
      case findRec ty of
        Just fixT -> pure $ Roll fixT $ As (Tag tag term) ty
        Nothing -> pure $ As (Tag tag term) ty

findRec :: Type -> Maybe Type
findRec (FuncT ty1 ty2) = findRec ty1 <|> findRec ty2
findRec (PairT ty1 ty2) = findRec ty1 <|> findRec ty2
findRec (TupleT tys) = foldr (<|>) Nothing (fmap findRec tys)
findRec (RecordT tys) = foldr (<|>) Nothing  $ fmap (findRec . snd) tys
findRec (SumT ty1 ty2) = findRec ty1 <|> findRec ty2
findRec (VariantT tys) = foldr (<|>) Nothing  $ fmap (findRec . snd) tys
findRec ty@(FixT _ _) = Just ty
findRec _ = Nothing

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
pFix = rword "fix" *> (Fix <$> pTerm)

-- TODO: Figure out how to prevent infinite recursion if I remove the reserved word.
pGet :: Parser Term
pGet = do
  rword "get"
  t1 <- pTerm
  dot
  var <- identifier <|> (show <$> integer)
  pure $ Get t1 var
