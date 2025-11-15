module Parser
  ( parseKind, parseType, parseTerm
  , Parser
  ) where

import Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void (Void)
import Control.Monad.Combinators.Expr

type Parser = Parsec Void String

-- | Space consumer (handles whitespace and comments)
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

-- | Lexeme: parse p and skip trailing whitespace
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Symbol: parse a specific string and skip trailing whitespace
symbol :: String -> Parser String
symbol = L.symbol sc

-- | Parse between parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Reserved words
reserved :: [String]
reserved = ["true", "false", "if", "then", "else", "forall", "Bool", "Nat",
            "zero", "succ", "pred", "iszero"]

-- | Parse an identifier (not a reserved word)
identifier :: Parser String
identifier = lexeme $ try $ do
  x <- (:) <$> letterChar <*> many alphaNumChar
  if x `elem` reserved
    then fail $ "keyword " ++ show x ++ " cannot be an identifier"
    else return x

-- | Parse a type variable (lowercase identifier)
tyVarP :: Parser TyVar
tyVarP = identifier

-- | Parse a term variable (lowercase identifier)
varP :: Parser Var
varP = identifier

-- | Parse a kind
-- κ ::= * | κ → κ | (κ)
kindP :: Parser Kind
kindP = makeExprParser kindTerm kindOps
  where
    kindTerm = parens kindP
           <|> (symbol "*" >> return KStar)

    kindOps = [ [InfixR (symbol "->" >> return KArr)] ]

parseKind :: String -> Either String Kind
parseKind input = case parse (sc >> kindP <* eof) "" input of
  Left err -> Left (errorBundlePretty err)
  Right k -> Right k

-- | Parse a type
-- τ ::= α | τ → τ | ∀α::κ. τ | λα::κ. τ | τ τ | Bool | Nat | (τ)
typeP :: Parser Type
typeP = makeExprParser typeTerm typeOps
  where
    typeTerm = parens typeP
           <|> forallType
           <|> tyLam
           <|> (symbol "Bool" >> return TyBool)
           <|> (symbol "Nat" >> return TyNat)
           <|> (TyVar <$> tyVarP)

    typeOps = [ [InfixL (return TyApp)]  -- Type application (left-associative, highest precedence)
              , [InfixR (symbol "->" >> return TyArr)] ]

    -- ∀α::κ. τ or forall α::κ. τ
    forallType = do
      _ <- symbol "forall" <|> symbol "∀"
      a <- tyVarP
      _ <- symbol "::"
      k <- kindP
      _ <- symbol "."
      t <- typeP
      return (TyForall a k t)

    -- λα::κ. τ or /\α::κ. τ
    tyLam = do
      _ <- symbol "/\\" <|> symbol "λ" <|> symbol "\\"
      a <- tyVarP
      _ <- symbol "::"
      k <- kindP
      _ <- symbol "."
      t <- typeP
      return (TyLam a k t)

parseType :: String -> Either String Type
parseType input = case parse (sc >> typeP <* eof) "" input of
  Left err -> Left (errorBundlePretty err)
  Right ty -> Right ty

-- | Parse a term
termP :: Parser Term
termP = makeExprParser termAtom termOps
  where
    termOps = [ [InfixL (return App)] ]  -- Application (left-associative)

    termAtom = parens termP
           <|> lamP
           <|> tyAbsP
           <|> ifP
           <|> (symbol "true" >> return TmTrue)
           <|> (symbol "false" >> return TmFalse)
           <|> (symbol "zero" >> return TmZero)
           <|> succP
           <|> predP
           <|> isZeroP
           <|> tyAppP
           <|> (Var <$> varP)

    -- λ(x:τ). t or \(x:τ). t
    lamP = do
      _ <- symbol "λ" <|> symbol "\\"
      _ <- symbol "("
      x <- varP
      _ <- symbol ":"
      ty <- typeP
      _ <- symbol ")"
      _ <- symbol "."
      t <- termP
      return (Lam x ty t)

    -- Λα::κ. t or /\α::κ. t
    tyAbsP = do
      _ <- symbol "Λ" <|> symbol "/\\"
      a <- tyVarP
      _ <- symbol "::"
      k <- kindP
      _ <- symbol "."
      t <- termP
      return (TyAbs a k t)

    -- t [τ]
    tyAppP = do
      t <- Var <$> try (varP <* symbol "[")
           <|> try (parens termP <* symbol "[")
      ty <- typeP
      _ <- symbol "]"
      return (TyAppTerm t ty)

    -- if t1 then t2 else t3
    ifP = do
      _ <- symbol "if"
      t1 <- termP
      _ <- symbol "then"
      t2 <- termP
      _ <- symbol "else"
      t3 <- termP
      return (TmIf t1 t2 t3)

    -- succ t
    succP = do
      _ <- symbol "succ"
      t <- termAtom
      return (TmSucc t)

    -- pred t
    predP = do
      _ <- symbol "pred"
      t <- termAtom
      return (TmPred t)

    -- iszero t
    isZeroP = do
      _ <- symbol "iszero"
      t <- termAtom
      return (TmIsZero t)

parseTerm :: String -> Either String Term
parseTerm input = case parse (sc >> termP <* eof) "" input of
  Left err -> Left (errorBundlePretty err)
  Right t -> Right t
