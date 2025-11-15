{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( parseTerm
  , parseTermEither
  , Parser
  ) where

import Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text (Text)
import Data.Void (Void)
import Control.Monad (void)

type Parser = Parsec Void Text

-- | Space consumer (skips whitespace and comments)
sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

-- | Lexeme parser (consumes trailing whitespace)
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Parse a specific symbol
symbol :: Text -> Parser Text
symbol = L.symbol sc

-- | Parse a variable name (lowercase identifier)
varName :: Parser Var
varName = lexeme $ do
  c <- lowerChar
  cs <- many alphaNumChar
  let name = c : cs
  return name

-- | Parse a lambda symbol (λ or \)
lambdaSymbol :: Parser ()
lambdaSymbol = void (symbol "λ" <|> symbol "\\")

-- | Parse parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Parse a term (handles left-associative application)
term :: Parser Term
term = do
  t <- atom
  ts <- many atom
  return $ foldl App t ts

-- | Parse an atomic term (no application)
atom :: Parser Term
atom = choice
  [ parens term
  , lambda
  , variable
  ]

-- | Parse a variable
variable :: Parser Term
variable = Var <$> varName

-- | Parse a lambda abstraction
-- Supports: λx. body, \x. body, λx -> body, or multiple args λx y z. body
lambda :: Parser Term
lambda = do
  lambdaSymbol
  vars <- some varName
  void (symbol "." <|> symbol "->")
  body <- term
  return $ foldr Lam body vars

-- | Parse a complete term (with leading/trailing whitespace)
parseTerm :: Text -> Either String Term
parseTerm input = case parseTermEither input of
  Left err -> Left err
  Right t -> Right t

-- | Parse a term, returning Either with error message
parseTermEither :: Text -> Either String Term
parseTermEither input =
  case runParser (sc *> term <* eof) "" input of
    Left err -> Left (errorBundlePretty err)
    Right t -> Right t
