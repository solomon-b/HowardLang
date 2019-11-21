module HowardLang.Parser.Token where

import Control.Monad.Reader

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import HowardLang.Parser.Combinators


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
