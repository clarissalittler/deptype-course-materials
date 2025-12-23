{-# LANGUAGE OverloadedStrings #-}
-- | Parser for NbE terms

module Parser
  ( parseTerm
  , parseFile
  ) where

import Syntax

import Control.Monad (void)
import Data.Void
import Data.List (elemIndex)
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

identifier :: Parser String
identifier = lexeme $ do
  c <- letterChar <|> char '_'
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c : cs
  if name `elem` reserved
    then fail $ "Reserved word: " ++ name
    else return name

reserved :: [String]
reserved = ["let", "in", "if", "then", "else", "Bool", "true", "false",
            "Nat", "zero", "suc", "natElim", "Type", "fun", "forall"]

-- Parser with name resolution

type Scope = [Name]

term :: Scope -> Parser Term
term scope = piType scope <|> lamTerm scope <|> letTerm scope <|> ifTerm scope <|> app scope

piType :: Scope -> Parser Term
piType scope = do
  void $ symbol "forall" <|> symbol "Π" <|> symbol "∀"
  void $ symbol "("
  x <- identifier
  void $ symbol ":"
  a <- term scope
  void $ symbol ")"
  void $ symbol "->" <|> symbol "→"
  b <- term (x : scope)
  return $ TPi x a b

lamTerm :: Scope -> Parser Term
lamTerm scope = do
  void $ symbol "\\" <|> symbol "λ" <|> symbol "fun"
  x <- identifier
  void $ symbol "."
  t <- term (x : scope)
  return $ TLam x t

letTerm :: Scope -> Parser Term
letTerm scope = do
  void $ symbol "let"
  x <- identifier
  void $ symbol ":"
  a <- term scope
  void $ symbol "="
  t <- term scope
  void $ symbol "in"
  u <- term (x : scope)
  return $ TLet x a t u

ifTerm :: Scope -> Parser Term
ifTerm scope = do
  void $ symbol "if"
  b <- term scope
  void $ symbol "then"
  t <- term scope
  void $ symbol "else"
  f <- term scope
  return $ TIf b t f

app :: Scope -> Parser Term
app scope = do
  f <- atom scope
  args <- many (try $ atom scope)
  return $ foldl TApp f args

atom :: Scope -> Parser Term
atom scope = choice
  [ parens (term scope)
  , TU <$ symbol "Type"
  , TBool <$ symbol "Bool"
  , TTrue <$ symbol "true"
  , TFalse <$ symbol "false"
  , TNat <$ symbol "Nat"
  , TZero <$ symbol "zero"
  , sucTerm scope
  , natElimTerm scope
  , varTerm scope
  ]

sucTerm :: Scope -> Parser Term
sucTerm scope = do
  void $ symbol "suc"
  n <- atom scope
  return $ TSuc n

natElimTerm :: Scope -> Parser Term
natElimTerm scope = do
  void $ symbol "natElim"
  p <- atom scope
  z <- atom scope
  s <- atom scope
  n <- atom scope
  return $ TNatElim p z s n

varTerm :: Scope -> Parser Term
varTerm scope = do
  x <- identifier
  case elemIndex x scope of
    Just i  -> return $ TVar i
    Nothing -> fail $ "Unbound variable: " ++ x

-- Entry points

parseTerm :: String -> Either String Term
parseTerm input = case parse (sc *> term [] <* eof) "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right t  -> Right t

parseFile :: FilePath -> IO (Either String Term)
parseFile path = do
  contents <- readFile path
  return $ parseTerm contents
