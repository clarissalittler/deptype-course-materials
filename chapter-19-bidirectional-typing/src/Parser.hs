{-# LANGUAGE OverloadedStrings #-}
-- | Parser for bidirectional terms

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

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

identifier :: Parser String
identifier = lexeme $ do
  c <- letterChar <|> char '_'
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c : cs
  if name `elem` reserved
    then fail $ "Reserved word: " ++ name
    else return name

reserved :: [String]
reserved = ["let", "in", "if", "then", "else", "true", "false",
            "zero", "suc", "natrec", "unit", "fst", "snd",
            "inl", "inr", "case", "of", "Bool", "Nat", "Unit",
            "forall", "fun", "lam"]

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
  , forallType
  , prodType
  , sumType
  , TyVar <$> identifier
  ]

forallType :: Parser Type
forallType = do
  void $ symbol "forall"
  a <- identifier
  void $ symbol "."
  t <- typeExpr
  return $ TyForall a t

prodType :: Parser Type
prodType = do
  void $ symbol "("
  t1 <- typeExpr
  void $ symbol ","
  t2 <- typeExpr
  void $ symbol ")"
  return $ TyProd t1 t2

sumType :: Parser Type
sumType = do
  void $ symbol "("
  t1 <- typeExpr
  void $ symbol "+"
  t2 <- typeExpr
  void $ symbol ")"
  return $ TySum t1 t2

-- Term parser

term :: Parser Term
term = choice
  [ try lamAnnTerm  -- Must try this before lamTerm (both start with \)
  , lamTerm
  , letTerm
  , ifTerm
  , caseTerm
  , tyLamTerm
  , app
  ]

lamTerm :: Parser Term
lamTerm = do
  void $ symbol "\\" <|> symbol "λ" <|> symbol "fun"
  x <- identifier
  void $ symbol "."
  e <- term
  return $ Lam x e

lamAnnTerm :: Parser Term
lamAnnTerm = do
  void $ symbol "\\" <|> symbol "λ" <|> symbol "fun"
  void $ symbol "("
  x <- identifier
  void $ symbol ":"
  t <- typeExpr
  void $ symbol ")"
  void $ symbol "."
  e <- term
  return $ LamAnn x t e

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

caseTerm :: Parser Term
caseTerm = do
  void $ symbol "case"
  scrut <- term
  void $ symbol "of"
  void $ symbol "inl"
  x1 <- identifier
  void $ symbol "->"
  e1 <- term
  void $ symbol "|"
  void $ symbol "inr"
  x2 <- identifier
  void $ symbol "->"
  e2 <- term
  return $ Case scrut x1 e1 x2 e2

tyLamTerm :: Parser Term
tyLamTerm = do
  void $ symbol "/\\" <|> symbol "Λ"
  a <- identifier
  void $ symbol "."
  e <- term
  return $ TyLam a e

app :: Parser Term
app = do
  f <- atom
  args <- many appArg
  return $ foldl applyArg f args
  where
    applyArg e (Left t) = TyApp e t
    applyArg e (Right e') = App e e'

appArg :: Parser (Either Type Term)
appArg = (Left <$> brackets typeExpr) <|> (Right <$> atom)

atom :: Parser Term
atom = choice
  [ parenExpr       -- handles (e), (e : T), and (e1, e2)
  , TmTrue <$ symbol "true"
  , TmFalse <$ symbol "false"
  , Zero <$ symbol "zero"
  , sucTerm
  , TmUnit <$ symbol "unit"
  , fstTerm
  , sndTerm
  , inlTerm
  , inrTerm
  , natrecTerm
  , Var <$> identifier
  ]

-- | Parse parenthesized expressions: (e), (e : T), or (e1, e2)
parenExpr :: Parser Term
parenExpr = do
  void $ symbol "("
  e <- term
  choice
    [ do  -- Annotation: (e : T)
        void $ symbol ":"
        t <- typeExpr
        void $ symbol ")"
        return $ Ann e t
    , do  -- Pair: (e1, e2)
        void $ symbol ","
        e2 <- term
        void $ symbol ")"
        return $ Pair e e2
    , do  -- Just parenthesized: (e)
        void $ symbol ")"
        return e
    ]

sucTerm :: Parser Term
sucTerm = do
  void $ symbol "suc"
  n <- atom
  return $ Suc n


fstTerm :: Parser Term
fstTerm = do
  void $ symbol "fst"
  e <- atom
  return $ Fst e

sndTerm :: Parser Term
sndTerm = do
  void $ symbol "snd"
  e <- atom
  return $ Snd e

inlTerm :: Parser Term
inlTerm = do
  void $ symbol "inl"
  e <- atom
  return $ Inl e

inrTerm :: Parser Term
inrTerm = do
  void $ symbol "inr"
  e <- atom
  return $ Inr e

natrecTerm :: Parser Term
natrecTerm = do
  void $ symbol "natrec"
  z <- atom
  s <- atom
  n <- atom
  return $ NatRec z s n


-- Entry points

parseTerm :: String -> Either String Term
parseTerm input = case parse (sc *> term <* eof) "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right t  -> Right t

parseType :: String -> Either String Type
parseType input = case parse (sc *> typeExpr <* eof) "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right t  -> Right t
