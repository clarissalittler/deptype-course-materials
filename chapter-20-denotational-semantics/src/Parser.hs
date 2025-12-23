{-# LANGUAGE OverloadedStrings #-}
-- | Parser for denotational semantics terms

module Parser
  ( parseTerm
  , parseType
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

identifier :: Parser String
identifier = try $ lexeme $ do
  c <- letterChar <|> char '_'
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c : cs
  if name `elem` reserved
    then fail $ "Reserved word: " ++ name
    else return name

reserved :: [String]
reserved = ["let", "in", "if", "then", "else", "true", "false",
            "fix", "suc", "pred", "iszero", "natrec", "unit", "zero",
            "Bool", "Nat", "Unit", "fun", "lam", "bottom"]

number :: Parser Integer
number = lexeme L.decimal

-- Type parser

typeExpr :: Parser Type
typeExpr = makeExprParser typeAtom ops
  where
    ops = [[InfixR (TyArr <$ symbol "->")]]

typeAtom :: Parser Type
typeAtom = choice
  [ parens typeExpr
  , TyBool <$ symbol "Bool"
  , TyNat <$ symbol "Nat"
  , TyUnit <$ symbol "Unit"
  ]

-- Term parser

term :: Parser Term
term = choice
  [ try lamTerm
  , letTerm
  , ifTerm
  , fixTerm
  , app
  ]

lamTerm :: Parser Term
lamTerm = do
  void $ symbol "\\" <|> symbol "λ" <|> symbol "fun"
  void $ symbol "("
  x <- identifier
  void $ symbol ":"
  t <- typeExpr
  void $ symbol ")"
  void $ symbol "."
  e <- term
  return $ Lam x t e

letTerm :: Parser Term
letTerm = do
  void $ symbol "let"
  x <- identifier
  void $ symbol "="
  e1 <- term
  void $ symbol "in"
  e2 <- term
  return $ Let x e1 e2

ifTerm :: Parser Term
ifTerm = do
  void $ symbol "if"
  cond <- term
  void $ symbol "then"
  thn <- term
  void $ symbol "else"
  els <- term
  return $ If cond thn els

fixTerm :: Parser Term
fixTerm = do
  void $ symbol "fix"
  e <- atom
  return $ Fix e

app :: Parser Term
app = do
  f <- atom
  args <- many atom
  return $ foldl App f args

atom :: Parser Term
atom = choice
  [ parens term
  , TmTrue <$ symbol "true"
  , TmFalse <$ symbol "false"
  , Zero <$ (symbol "0" <|> symbol "zero")
  , sucTerm
  , predTerm
  , iszeroTerm
  , natrecTerm
  , TmUnit <$ (symbol "unit" <|> symbol "()")
  , bottomTerm
  , numLit
  , Var <$> identifier
  ]

sucTerm :: Parser Term
sucTerm = do
  void $ symbol "suc"
  n <- atom
  return $ Suc n

predTerm :: Parser Term
predTerm = do
  void $ symbol "pred"
  n <- atom
  return $ Pred n

iszeroTerm :: Parser Term
iszeroTerm = do
  void $ symbol "iszero"
  n <- atom
  return $ IsZero n

natrecTerm :: Parser Term
natrecTerm = do
  void $ symbol "natrec"
  z <- atom
  s <- atom
  n <- atom
  return $ NatRec z s n

bottomTerm :: Parser Term
bottomTerm = do
  void $ symbol "⊥" <|> symbol "bottom"
  t <- typeAtom
  return $ Bottom t

-- Parse numeric literals as church-like nats
numLit :: Parser Term
numLit = do
  n <- number
  return $ toNat n
  where
    toNat 0 = Zero
    toNat k = Suc (toNat (k - 1))

-- Entry points

parseTerm :: String -> Either String Term
parseTerm input = case parse (sc *> term <* eof) "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right t  -> Right t

parseType :: String -> Either String Type
parseType input = case parse (sc *> typeExpr <* eof) "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right t  -> Right t
