module Parser
  ( parseTerm
  , parsePattern
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
reserved = ["Type", "Nat", "Bool", "Unit", "Empty", "true", "false", "zero",
            "succ", "if", "then", "else", "fst", "snd", "Pi", "Sigma",
            "refl", "Eq", "match", "with", "natElim", "boolElim", "unitElim",
            "emptyElim", "J"]

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

-- | Natural number literal
natLit :: Parser Int
natLit = lexeme L.decimal

-- | Parse a term
termP :: Parser Term
termP = makeExprParser termAtom termOps
  where
    termOps =
      [ [InfixL (return App)]
      , [InfixR (piArrow <$ (symbol "->" <|> symbol "→"))]
      ]

    termAtom = parens termP
           <|> universeP
           <|> lambdaP
           <|> piP
           <|> sigmaP
           <|> pairP
           <|> fstP
           <|> sndP
           <|> eqP
           <|> reflP
           <|> jP
           <|> matchP
           <|> natElimP
           <|> boolElimP
           <|> unitElimP
           <|> emptyElimP
           <|> ifP
           <|> (symbol "Nat" >> return Nat)
           <|> (symbol "Bool" >> return Bool)
           <|> (symbol "Unit" >> return Unit)
           <|> (symbol "Empty" >> return Empty)
           <|> (symbol "true" >> return TmTrue)
           <|> (symbol "false" >> return TmFalse)
           <|> (symbol "TT" >> return TT)
           <|> zeroOrNatLit
           <|> succP
           <|> conP
           <|> indP
           <|> (Var <$> varP)

    piArrow a b = Pi "_" a b

    -- Type i
    universeP = do
      _ <- symbol "Type"
      level <- option 0 natLit
      return (Universe level)

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

    -- Π(x:A). B  or  Pi(x:A). B
    piP = do
      _ <- symbol "Π" <|> symbol "Pi"
      _ <- symbol "("
      x <- varP
      _ <- symbol ":"
      a <- termP
      _ <- symbol ")"
      _ <- symbol "."
      b <- termP
      return (Pi x a b)

    -- Σ(x:A). B  or  Sigma(x:A). B
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

    -- Eq A x y
    eqP = do
      _ <- symbol "Eq"
      a <- termAtom
      x <- termAtom
      y <- termAtom
      return (Eq a x y)

    -- refl x
    reflP = do
      _ <- symbol "refl"
      x <- termAtom
      return (Refl x)

    -- J(A, C, p, x, y, eq)
    jP = do
      _ <- symbol "J"
      _ <- symbol "("
      a <- termP
      _ <- symbol ","
      c <- termP
      _ <- symbol ","
      p <- termP
      _ <- symbol ","
      x <- termP
      _ <- symbol ","
      y <- termP
      _ <- symbol ","
      eq <- termP
      _ <- symbol ")"
      return (J a c p x y eq)

    -- match t with | pat -> rhs | ...
    matchP = do
      _ <- symbol "match"
      t <- termP
      _ <- symbol "with"
      branches <- many branchP
      return (Match t branches)

    branchP = do
      _ <- symbol "|"
      pat <- patternP
      _ <- symbol "->"
      rhs <- termP
      return (pat, rhs)

    -- natElim(P, z, s, n)
    natElimP = do
      _ <- symbol "natElim"
      _ <- symbol "("
      p <- termP
      _ <- symbol ","
      z <- termP
      _ <- symbol ","
      s <- termP
      _ <- symbol ","
      n <- termP
      _ <- symbol ")"
      return (NatElim p z s n)

    -- boolElim(P, t, f, b)
    boolElimP = do
      _ <- symbol "boolElim"
      _ <- symbol "("
      p <- termP
      _ <- symbol ","
      t <- termP
      _ <- symbol ","
      f <- termP
      _ <- symbol ","
      b <- termP
      _ <- symbol ")"
      return (BoolElim p t f b)

    -- unitElim(P, u, x)
    unitElimP = do
      _ <- symbol "unitElim"
      _ <- symbol "("
      p <- termP
      _ <- symbol ","
      u <- termP
      _ <- symbol ","
      x <- termP
      _ <- symbol ")"
      return (UnitElim p u x)

    -- emptyElim(P, e)
    emptyElimP = do
      _ <- symbol "emptyElim"
      _ <- symbol "("
      p <- termP
      _ <- symbol ","
      e <- termP
      _ <- symbol ")"
      return (EmptyElim p e)

    -- if t then t else t
    ifP = do
      _ <- symbol "if"
      t1 <- termP
      _ <- symbol "then"
      t2 <- termP
      _ <- symbol "else"
      t3 <- termP
      return (BoolElim (Lam "_" Bool (Universe 0)) t2 t3 t1)

    -- zero or numeric literal
    zeroOrNatLit = do
      n <- (0 <$ symbol "zero") <|> natLit
      return (natFromInt n)

    natFromInt n
      | n <= 0 = Zero
      | otherwise = Succ (natFromInt (n - 1))

    -- succ t
    succP = do
      _ <- symbol "succ"
      t <- termAtom
      return (Succ t)

    -- Constructor application: Con name args
    conP = try $ do
      name <- upperIdentifier
      args <- many termAtom
      return (Con name args)

    -- Inductive type reference: Ind name
    indP = try $ do
      name <- upperIdentifier
      return (Ind name)

    upperIdentifier = lexeme $ try $ do
      x <- (:) <$> upperChar <*> many alphaNumChar
      return x

-- | Parse a pattern
patternP :: Parser Pattern
patternP = pconP <|> pvarP <|> pwildP
  where
    pvarP = PVar <$> varP
    pwildP = symbol "_" >> return PWild
    pconP = try $ do
      name <- upperIdentifier
      args <- many patternAtom
      return (PCon name args)

    patternAtom = parens patternP <|> pvarP <|> pwildP

    upperIdentifier = lexeme $ try $ do
      x <- (:) <$> upperChar <*> many alphaNumChar
      return x

parseTerm :: String -> Either String Term
parseTerm input = case parse (sc >> termP <* eof) "" input of
  Left err -> Left (errorBundlePretty err)
  Right t -> Right t

parsePattern :: String -> Either String Pattern
parsePattern input = case parse (sc >> patternP <* eof) "" input of
  Left err -> Left (errorBundlePretty err)
  Right p -> Right p
