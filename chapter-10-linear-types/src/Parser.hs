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

sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

reserved :: Text -> Parser ()
reserved w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

reservedWords :: [Text]
reservedWords =
  [ "true", "false", "if", "then", "else"
  , "succ", "pred", "iszero"
  , "Bool", "Nat", "let", "in"
  , "fst", "snd"
  ]

identifier :: Parser String
identifier = (lexeme . try) $ do
  x <- (:) <$> letterChar <*> many alphaNumChar
  if T.pack x `elem` reservedWords
    then fail $ "keyword " ++ show x ++ " cannot be an identifier"
    else return x

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- =============================================================================
-- Type Parser
-- =============================================================================

parseType :: Text -> Either ParseError Type
parseType = parse (sc *> pType <* eof) "<input>"

pType :: Parser Type
pType = makeExprParser pTypeAtom typeOperators

typeOperators :: [[Operator Parser Type]]
typeOperators =
  [ [ InfixR (TyFun One <$ symbol "-o")
    , InfixR (TyFun Many <$ symbol "->")
    ]
  , [ InfixL (TyPair <$ symbol "*") ]
  ]

pTypeAtom :: Parser Type
pTypeAtom = choice
  [ TyBool <$ reserved "Bool"
  , TyNat <$ reserved "Nat"
  , TyUnit <$ symbol "()"
  , TyBang <$> (symbol "!" *> pTypeAtom)
  , TyVar <$> identifier
  , parens pType
  ]

-- =============================================================================
-- Term Parser
-- =============================================================================

parseTerm :: Text -> Either ParseError Term
parseTerm = parse (sc *> pTerm <* eof) "<input>"

parseFile :: FilePath -> Text -> Either ParseError Term
parseFile = parse (sc *> pTerm <* eof)

pTerm :: Parser Term
pTerm = pLet <|> pLetPair <|> pLetBang <|> pApp

pApp :: Parser Term
pApp = do
  terms <- some pAtom
  return $ foldl1 App terms

pAtom :: Parser Term
pAtom = choice
  [ pLambda
  , pIf
  , TmTrue <$ reserved "true"
  , TmFalse <$ reserved "false"
  , TmZero <$ symbol "0"
  , TmSucc <$> (reserved "succ" *> pAtom)
  , TmPred <$> (reserved "pred" *> pAtom)
  , TmIsZero <$> (reserved "iszero" *> pAtom)
  , TmUnit <$ symbol "()"
  , TmBang <$> (symbol "!" *> pAtom)
  , pPairOrParens
  , Var <$> identifier
  ]

pLambda :: Parser Term
pLambda = do
  _ <- symbol "\\" <|> symbol "λ"
  x <- identifier
  _ <- symbol ":"
  m <- pMult
  ty <- pType
  _ <- symbol "."
  t <- pTerm
  return $ Lam x m ty t

pMult :: Parser Mult
pMult = choice
  [ One <$ symbol "1"
  , Many <$ symbol "w"
  , pure Many  -- Default to Many if not specified
  ]

pIf :: Parser Term
pIf = do
  reserved "if"
  t1 <- pTerm
  reserved "then"
  t2 <- pTerm
  reserved "else"
  t3 <- pTerm
  return $ TmIf t1 t2 t3

pLet :: Parser Term
pLet = do
  reserved "let"
  x <- identifier
  _ <- symbol ":"
  m <- pMult
  _ <- symbol "="
  t1 <- pTerm
  reserved "in"
  t2 <- pTerm
  return $ TmLet x m t1 t2

pLetPair :: Parser Term
pLetPair = try $ do
  reserved "let"
  _ <- symbol "("
  x <- identifier
  _ <- symbol ","
  y <- identifier
  _ <- symbol ")"
  _ <- symbol "="
  t1 <- pTerm
  reserved "in"
  t2 <- pTerm
  return $ TmLetPair x y t1 t2

pLetBang :: Parser Term
pLetBang = try $ do
  reserved "let"
  _ <- symbol "!"
  x <- identifier
  _ <- symbol "="
  t1 <- pTerm
  reserved "in"
  t2 <- pTerm
  return $ TmLetBang x t1 t2

pPairOrParens :: Parser Term
pPairOrParens = do
  _ <- symbol "("
  t1 <- pTerm
  choice
    [ do
        _ <- symbol ","
        t2 <- pTerm
        _ <- symbol ")"
        return $ TmPair t1 t2
    , symbol ")" >> return t1
    ]
