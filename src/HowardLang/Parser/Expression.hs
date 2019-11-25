module HowardLang.Parser.Expression where

import Control.Applicative hiding (some, many)
import Control.Monad.Reader

import Lens.Micro

import Data.Functor
import Data.List
import Data.Monoid

import Text.Megaparsec
import Text.Megaparsec.Char

import HowardLang.Types
import HowardLang.Parser.Combinators
import HowardLang.Parser.Token
import HowardLang.Typechecker (typeSubstTop)


-- | Composed Parser

-- TODO: Parser blows up with out of scope Vars
pValues :: Parser Term
pValues = pTuple <|> pRecord <|> pPair <|> pUnit <|> pBool <|> pNat <|> pPeano <|> pVar

pStmts :: Parser Term
pStmts = pLetRec <|> pFix <|> pGet <|> pVariantCase <|> pTag <|> pCase <|> pAbs <|> pLet <|> pAs <|> pFst <|> pSnd

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
pTupleT = parens $ do
  ty <- parseType
  comma
  tys <- parseType `sepBy1` comma
  pure $ TupleT (ty:tys)

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
  t1 <- try (parens parseType) <|> start
  mT2 <- end
  case mT2 of
    Epsilon -> pure t1
    PairTok t2 -> pure $ PairT t1 t2
    ArrowTok t2 -> pure $ FuncT t1 t2

start :: Parser Type
start = pFixT <|> pUnitT <|> pNatT <|> pBoolT <|> pVariantT <|> pTupleT <|> pRecordT <|> pVarT

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
pTuple = parens $ do
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
  If t1 t2 <$> pTerm

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

pLetRec :: Parser Term
pLetRec = do
  rword "letrec"
  var <- identifier
  params <- optional pLetParams
  rword "="
  t1 <- parseAbsWrappedTerm params
  rword "in"
  t2 <- bindLocalVar var pTerm
  pure $ Let var (FixLet t1) t2
{-
TODO: Recursion Sugar:
I want to be able to parse this:
let f (x : Nat) (y : Nat) = case x of Z => y | (S n) => f n (S y) in f
And detect the recursion and construct this:
Let "f" (Fix (Abs "rec" (FuncT NatT (FuncT NatT NatT)) (Abs "x" "NatT" (Abs "y" NatT <BODY>))))
-}

pFst :: Parser Term
pFst = rword "fst" *> (Fst <$> pTerm)

pSnd :: Parser Term
pSnd = rword "snd" *> (Snd <$> pTerm)

-- TODO Remove along with Nats when I have casing on recursive types and data type bindings/aliases
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
      case findRecType ty of
        Just fixT -> pure $ Roll fixT t1
        Nothing -> pure $ As t1 ty
    Nothing -> pure t1
  where
    variant :: Parser Term
    variant = Tag <$> constructor <*> pTerm
    enum :: Parser Term
    enum = Tag <$> constructor <*> pure Unit

findRecType :: Type -> Maybe Type
findRecType (FuncT ty1 ty2) = findRecType ty1 <|> findRecType ty2
findRecType (PairT ty1 ty2) = findRecType ty1 <|> findRecType ty2
findRecType (TupleT tys) = foldr (<|>) Nothing (fmap findRecType tys)
findRecType (RecordT tys) = foldr (<|>) Nothing  $ fmap (findRecType . snd) tys
findRecType (VariantT tys) = foldr (<|>) Nothing  $ fmap (findRecType . snd) tys
findRecType ty@(FixT _ _) = Just ty
findRecType _ = Nothing

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

pFix :: Parser Term
pFix = rword "fix" *> (FixLet <$> pTerm)

-- TODO: Figure out how to prevent infinite recursion if I remove the reserved word.
pGet :: Parser Term
pGet = do
  rword "get"
  t1 <- pTerm
  dot
  var <- identifier <|> (show <$> integer)
  pure $ Get t1 var
