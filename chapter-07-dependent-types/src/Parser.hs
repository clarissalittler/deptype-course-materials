module Parser
  ( parseTerm
  , Parser
  ) where

import Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void (Void)
import Control.Monad.Combinators.Expr

type Parser = Parsec Void String

-- | Space consumer
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

-- | Lexeme
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Symbol
symbol :: String -> Parser String
symbol = L.symbol sc

-- | Parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Reserved words
reserved :: [String]
reserved = ["Type", "Nat", "Bool", "true", "false", "zero", "succ",
            "if", "then", "else", "fst", "snd", "Pi", "Sigma"]

-- | Identifier
identifier :: Parser String
identifier = lexeme $ try $ do
  x <- (:) <$> letterChar <*> many alphaNumChar
  if x `elem` reserved
    then fail $ "keyword " ++ show x ++ " cannot be an identifier"
    else return x

-- | Variable
varP :: Parser Name
varP = identifier

-- | Parse a term
termP :: Parser Term
termP = makeExprParser termAtom termOps
  where
    termOps = [[InfixL (return App)]]

    termAtom = pairP
           <|> parens termP
           <|> lambdaP
           <|> piP
           <|> sigmaP
           <|> fstP
           <|> sndP
           <|> ifP
           <|> (symbol "Type" >> return Type)
           <|> (symbol "Nat" >> return Nat)
           <|> (symbol "Bool" >> return Bool)
           <|> (symbol "true" >> return TmTrue)
           <|> (symbol "false" >> return TmFalse)
           <|> (symbol "zero" >> return Zero)
           <|> succP
           <|> (Var <$> varP)

    -- λ(x:A). t
    lambdaP = do
      _ <- symbol "λ" <|> symbol "\\"
      _ <- symbol "("
      x <- varP
      _ <- symbol ":"
      a <- termP
      _ <- symbol ")"
      _ <- symbol "."
      t <- termP
      return (Lam x a t)

    -- Π(x:A). B  or  (x:A) -> B
    piP = try piSymbol <|> try arrowSugar
      where
        piSymbol = do
          _ <- symbol "Π" <|> symbol "Pi"
          _ <- symbol "("
          x <- varP
          _ <- symbol ":"
          a <- termP
          _ <- symbol ")"
          _ <- symbol "."
          b <- termP
          return (Pi x a b)

        arrowSugar = do
          _ <- symbol "("
          x <- varP
          _ <- symbol ":"
          a <- termP
          _ <- symbol ")"
          _ <- symbol "->"
          b <- termP
          return (Pi x a b)

    -- Σ(x:A). B
    sigmaP = do
      _ <- symbol "Σ" <|> symbol "Sigma"
      _ <- symbol "("
      x <- varP
      _ <- symbol ":"
      a <- termP
      _ <- symbol ")"
      _ <- symbol "."
      b <- termP
      return (Sigma x a b)

    -- (t₁, t₂)
    pairP = try $ do
      _ <- symbol "("
      t1 <- termP
      _ <- symbol ","
      t2 <- termP
      _ <- symbol ")"
      return (Pair t1 t2)

    -- fst t
    fstP = do
      _ <- symbol "fst"
      t <- termAtom
      return (Fst t)

    -- snd t
    sndP = do
      _ <- symbol "snd"
      t <- termAtom
      return (Snd t)

    -- if t then t else t
    ifP = do
      _ <- symbol "if"
      t1 <- termP
      _ <- symbol "then"
      t2 <- termP
      _ <- symbol "else"
      t3 <- termP
      return (If t1 t2 t3)

    -- succ t
    succP = do
      _ <- symbol "succ"
      t <- termAtom
      return (Succ t)

parseTerm :: String -> Either String Term
parseTerm input = case parse (sc >> termP <* eof) "" input of
  Left err -> Left (errorBundlePretty err)
  Right t -> Right t
