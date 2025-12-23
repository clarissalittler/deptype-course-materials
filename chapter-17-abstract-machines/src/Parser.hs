{-# LANGUAGE OverloadedStrings #-}
-- | Parser for abstract machine terms

module Parser
  ( parseTerm
  , parseFile
  ) where

import Syntax

import Control.Monad (void)
import Control.Monad.Combinators.Expr
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

-- Lexer

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

integer :: Parser Integer
integer = lexeme L.decimal

identifier :: Parser String
identifier = lexeme $ do
  c <- letterChar <|> char '_'
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c : cs
  if name `elem` reserved
    then fail $ "Reserved word: " ++ name
    else return name

reserved :: [String]
reserved = ["let", "in", "if0", "then", "else", "fix", "lam", "fn"]

-- Term parser

term :: Parser Term
term = makeExprParser atom ops
  where
    ops =
      [ [InfixL (TmMul <$ symbol "*")]
      , [InfixL (TmAdd <$ symbol "+"), InfixL (TmSub <$ symbol "-")]
      ]

atom :: Parser Term
atom = choice
  [ parens term
  , lamTerm
  , letTerm
  , if0Term
  , fixTerm
  , intLit
  , var
  ] >>= apps
  where
    apps t = do
      args <- many (try atomNoApp)
      return $ foldl TmApp t args

    -- Atom without recursive application (to avoid left recursion)
    atomNoApp = choice
      [ parens term
      , intLit
      , var
      ]

lamTerm :: Parser Term
lamTerm = do
  void $ symbol "\\" <|> symbol "λ" <|> symbol "lam" <|> symbol "fn"
  x <- identifier
  void $ symbol "."
  t <- term
  return $ TmLam x t

letTerm :: Parser Term
letTerm = do
  void $ symbol "let"
  x <- identifier
  void $ symbol "="
  t1 <- term
  void $ symbol "in"
  t2 <- term
  return $ TmLet x t1 t2

if0Term :: Parser Term
if0Term = do
  void $ symbol "if0"
  t1 <- term
  void $ symbol "then"
  t2 <- term
  void $ symbol "else"
  t3 <- term
  return $ TmIf0 t1 t2 t3

fixTerm :: Parser Term
fixTerm = do
  void $ symbol "fix"
  t <- atom
  return $ TmFix t

intLit :: Parser Term
intLit = TmInt <$> integer

var :: Parser Term
var = TmVar <$> identifier

-- Entry points

parseTerm :: String -> Either String Term
parseTerm input = case parse (sc *> term <* eof) "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right t  -> Right t

parseFile :: FilePath -> IO (Either String Term)
parseFile path = do
  contents <- readFile path
  return $ parseTerm contents
