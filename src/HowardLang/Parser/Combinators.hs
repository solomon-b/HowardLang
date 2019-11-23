{-# LANGUAGE MultiParamTypeClasses #-}
module HowardLang.Parser.Combinators where

import Control.Applicative
import Control.Monad.Reader hiding (fail)

import Lens.Micro

import Data.Semigroup()
import Data.Functor.Identity
import Data.Text()
import Text.Parser.Combinators (try, (<?>))

import qualified Data.String
import qualified Data.Char
import qualified Data.Text
import qualified Control.Monad.Fail
import qualified Text.Megaparsec
import qualified Text.Megaparsec.Char
import qualified Text.Parser.Combinators
import qualified Text.Parser.Char
import qualified Text.Parser.Token
import qualified Text.Parser.Token.Style

import HowardLang.Types (UnboundError, ParseErr, Term, Type, Varname, Err(..))

data PBindings = PBindings { _bindings :: [Varname], _types :: [Type]}

instance Semigroup PBindings where
  (<>) (PBindings xs ys) (PBindings xs' ys') = PBindings (xs <> xs') (ys <> ys')

instance Monoid PBindings where
  mempty = PBindings [] []
  mappend = (<>)

newtype Parser a = Parser { unParser :: Text.Megaparsec.ParsecT UnboundError String (Reader PBindings) a }
  deriving (Functor, Applicative, Alternative, Monad, Control.Monad.Fail.MonadFail, MonadReader PBindings)

handleParseErr :: Either ParseErr Term -> Either Err Term
handleParseErr = either (Left . P) Right

runParse :: Parser Term -> String -> Either Err Term
runParse (Parser p) =
  handleParseErr . runIdentity . flip runReaderT mempty . Text.Megaparsec.runParserT p mempty

-- Context Manipulation --
bindings :: Lens' PBindings [Varname]
bindings = lens _bindings (\s b -> s { _bindings = b })

types :: Lens' PBindings [Type]
types = lens _types (\s b -> s { _types = b })

bindVar :: Varname -> PBindings -> PBindings
bindVar var = over bindings ((:) var)

bindType :: Type -> PBindings -> PBindings
bindType ty = over types ((:) ty)

bindLocalVar :: Varname -> Parser a -> Parser a
bindLocalVar var = local (bindVar var)

bindRecursiveType :: Type -> Parser a -> Parser a
bindRecursiveType ty = local (bindType ty)

-- Used for debugging combinators:
run :: Parser a -> String -> Either ParseErr a
run (Parser p) = runIdentity . flip runReaderT mempty . Text.Megaparsec.runParserT p mempty


instance MonadPlus Parser where
  mzero = empty
  mplus = (<|>)

instance Text.Megaparsec.MonadParsec UnboundError String Parser where
  failure u e               = Parser (Text.Megaparsec.failure u e)
  fancyFailure e            = Parser (Text.Megaparsec.fancyFailure e)
  label l (Parser p)        = Parser (Text.Megaparsec.label l p)
  hidden (Parser p)         = Parser (Text.Megaparsec.hidden p)
  try (Parser p)            = Parser (Text.Megaparsec.try p)
  lookAhead (Parser p)      = Parser (Text.Megaparsec.lookAhead p)
  notFollowedBy (Parser p)  = Parser (Text.Megaparsec.notFollowedBy p)
  withRecovery e (Parser p) = Parser (Text.Megaparsec.withRecovery (unParser . e) p)
  observing (Parser p)      = Parser (Text.Megaparsec.observing p)
  eof                       = Parser Text.Megaparsec.eof
  token f e                 = Parser (Text.Megaparsec.token f e)
  tokens f ts               = Parser (Text.Megaparsec.tokens f ts)
  takeWhileP s f            = Parser (Text.Megaparsec.takeWhileP s f)
  takeWhile1P s f           = Parser (Text.Megaparsec.takeWhile1P s f)
  takeP s n                 = Parser (Text.Megaparsec.takeP s n)
  getParserState            = Parser Text.Megaparsec.getParserState
  updateParserState f       = Parser (Text.Megaparsec.updateParserState f)

instance Semigroup a => Semigroup (Parser a) where
  (<>) = liftA2 (<>)

instance (Semigroup a, Monoid a) => Monoid (Parser a) where
    mempty = pure mempty

instance Data.String.IsString a => Data.String.IsString (Parser a) where
    fromString x = Data.String.fromString x <$ Text.Megaparsec.Char.string (Data.String.fromString x)

instance Text.Parser.Combinators.Parsing Parser where
  try           = Text.Megaparsec.try
  (<?>)         = (Text.Megaparsec.<?>)
  skipMany      = Text.Megaparsec.skipMany
  skipSome      = Text.Megaparsec.skipSome
  unexpected    = fail
  eof           = Parser Text.Megaparsec.eof
  notFollowedBy = Text.Megaparsec.notFollowedBy

instance Text.Parser.Char.CharParsing Parser where
  satisfy = Parser . Text.Megaparsec.satisfy
  char    = Text.Megaparsec.Char.char
  notChar = Text.Megaparsec.Char.char
  anyChar = Text.Megaparsec.anySingle
  string  = Text.Megaparsec.Char.string
  text    = fmap Data.Text.pack . Text.Megaparsec.Char.string . Data.Text.unpack

instance Text.Parser.Token.TokenParsing Parser where
  someSpace =
      Text.Parser.Token.Style.buildSomeSpaceParser
          (Parser (Text.Megaparsec.skipSome (Text.Megaparsec.satisfy Data.Char.isSpace)))
          Text.Parser.Token.Style.haskellCommentStyle
  highlight _ = id
  semi = Text.Parser.Token.token (Text.Megaparsec.Char.char ';' <?> ";")
