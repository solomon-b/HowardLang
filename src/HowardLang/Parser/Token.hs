module HowardLang.Parser.Token where

import Control.Applicative
import Control.Monad.Reader

import Text.Parser.Combinators (Parsing(..))

import qualified Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer
import qualified Text.Parser.Combinators
import qualified Text.Parser.Token

import HowardLang.Parser.Combinators


between :: Parser bra -> Parser ket -> Parser a -> Parser a
between = Text.Parser.Combinators.between

symbol :: String -> Parser String
symbol = Text.Megaparsec.Char.Lexer.symbol whitespace

quoted :: Parser a -> Parser a
quoted = between (symbol "\"") (symbol "\"")

whitespace :: Parser ()
whitespace = Text.Parser.Token.whiteSpace

lexeme :: Parser a -> Parser a
lexeme = Text.Megaparsec.Char.Lexer.lexeme whitespace

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
integer = lexeme Text.Parser.Token.decimal

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
rword w = (lexeme . try) (Text.Megaparsec.Char.string w *> notFollowedBy Text.Megaparsec.Char.alphaNumChar)

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
      , "tag"
      ]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p :: Parser String
    p = (:) <$> Text.Megaparsec.Char.letterChar <*> many Text.Megaparsec.Char.alphaNumChar
    check :: String -> Parser String
    check str = if str `elem` rws
                 then fail $ "keyword " ++ show str ++ " cannot be an identifier"
                 else pure str

constructor :: Parser String
constructor = (lexeme . try) (p >>= check)
  where
    p :: Parser String
    p = (:) <$> Text.Megaparsec.Char.upperChar <*> many Text.Megaparsec.Char.alphaNumChar
    check :: String -> Parser String
    check str = do
      ctx <- asks _bindings
      if str `elem` ctx ++ rws
        then fail $ show str ++ " is already bound"
        else pure str
