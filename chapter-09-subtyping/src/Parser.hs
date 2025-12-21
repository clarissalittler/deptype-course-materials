{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( -- * Parsing
    parseTerm
  , parseType
  , parseFile
    -- * Parser type
  , Parser
  , ParseError
  ) where

import Syntax

import Control.Monad.Combinators.Expr
import Data.Void
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Text (Text)
import qualified Data.Text as T

-- =============================================================================
-- Parser Type
-- =============================================================================

type Parser = Parsec Void Text
type ParseError = ParseErrorBundle Text Void

-- =============================================================================
-- Lexer
-- =============================================================================

-- | Space consumer (handles comments and whitespace)
sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

-- | Lexeme wrapper
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Symbol parser
symbol :: Text -> Parser Text
symbol = L.symbol sc

-- | Reserved words
reserved :: Text -> Parser ()
reserved w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

-- | List of reserved words
reservedWords :: [Text]
reservedWords =
  [ "true", "false", "if", "then", "else"
  , "succ", "pred", "iszero"
  , "Bool", "Nat", "Top", "Bot"
  , "as"
  ]

-- | Identifier parser (not a reserved word)
identifier :: Parser String
identifier = (lexeme . try) $ do
  x <- (:) <$> letterChar <*> many alphaNumChar
  if T.pack x `elem` reservedWords
    then fail $ "keyword " ++ show x ++ " cannot be an identifier"
    else return x

-- | Parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Braces
braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

-- =============================================================================
-- Type Parser
-- =============================================================================

parseType :: Text -> Either ParseError Type
parseType = parse (sc *> pType <* eof) "<input>"

-- | Parse a type
pType :: Parser Type
pType = makeExprParser pTypeAtom typeOperators

typeOperators :: [[Operator Parser Type]]
typeOperators =
  [ [ InfixR (TyArr <$ symbol "->") ]
  ]

-- | Parse atomic types
pTypeAtom :: Parser Type
pTypeAtom = choice
  [ TyBool <$ reserved "Bool"
  , TyNat <$ reserved "Nat"
  , TyTop <$ reserved "Top"
  , TyBot <$ reserved "Bot"
  , TyRecord <$> pRecordType
  , TyVar <$> identifier
  , parens pType
  ]

-- | Parse a record type: {l1: T1, l2: T2, ...}
pRecordType :: Parser (Map Label Type)
pRecordType = braces $ do
  fields <- pTypeField `sepBy` symbol ","
  return $ Map.fromList fields

pTypeField :: Parser (Label, Type)
pTypeField = do
  l <- identifier
  _ <- symbol ":"
  ty <- pType
  return (l, ty)

-- =============================================================================
-- Term Parser
-- =============================================================================

parseTerm :: Text -> Either ParseError Term
parseTerm = parse (sc *> pTerm <* eof) "<input>"

parseFile :: FilePath -> Text -> Either ParseError Term
parseFile = parse (sc *> pTerm <* eof)

-- | Parse a term (handles application and ascription)
pTerm :: Parser Term
pTerm = do
  t <- pApp
  -- Check for ascription
  option t (TmAscribe t <$> (reserved "as" *> pType))

-- | Parse application (left-associative)
pApp :: Parser Term
pApp = do
  terms <- some pProjection
  return $ foldl1 App terms

-- | Parse projection (left-associative)
pProjection :: Parser Term
pProjection = do
  t <- pAtom
  projs <- many (symbol "." *> identifier)
  return $ foldl TmProj t projs

-- | Parse atomic terms
pAtom :: Parser Term
pAtom = choice
  [ pLambda
  , pIf
  , pTrue
  , pFalse
  , pZero
  , pSucc
  , pPred
  , pIsZero
  , pRecord
  , Var <$> identifier
  , parens pTerm
  ]

-- | Parse lambda: λx:T. t  or  \x:T. t
pLambda :: Parser Term
pLambda = do
  _ <- symbol "\\" <|> symbol "λ"
  x <- identifier
  _ <- symbol ":"
  ty <- pType
  _ <- symbol "."
  t <- pTerm
  return $ Lam x ty t

-- | Parse if-then-else
pIf :: Parser Term
pIf = do
  reserved "if"
  t1 <- pTerm
  reserved "then"
  t2 <- pTerm
  reserved "else"
  t3 <- pTerm
  return $ TmIf t1 t2 t3

pTrue :: Parser Term
pTrue = TmTrue <$ reserved "true"

pFalse :: Parser Term
pFalse = TmFalse <$ reserved "false"

pZero :: Parser Term
pZero = TmZero <$ symbol "0"

pSucc :: Parser Term
pSucc = TmSucc <$> (reserved "succ" *> pAtom)

pPred :: Parser Term
pPred = TmPred <$> (reserved "pred" *> pAtom)

pIsZero :: Parser Term
pIsZero = TmIsZero <$> (reserved "iszero" *> pAtom)

-- | Parse a record: {l1 = t1, l2 = t2, ...}
pRecord :: Parser Term
pRecord = braces $ do
  fields <- pTermField `sepBy` symbol ","
  return $ TmRecord $ Map.fromList fields

pTermField :: Parser (Label, Term)
pTermField = do
  l <- identifier
  _ <- symbol "="
  t <- pTerm
  return (l, t)
