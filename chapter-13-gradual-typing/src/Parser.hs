{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( -- * Parsing
    parseTerm
  , parseType
    -- * Errors
  , ParseError
  ) where

import Syntax

import Data.Void (Void)
import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- =============================================================================
-- Parser Types
-- =============================================================================

type Parser = Parsec Void Text
type ParseError = ParseErrorBundle Text Void

-- =============================================================================
-- Lexer
-- =============================================================================

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

angles :: Parser a -> Parser a
angles = between (symbol "<") (symbol ">")

reserved :: [Text]
reserved = ["true", "false", "if", "then", "else", "succ", "pred", "iszero",
            "let", "in", "Bool", "Nat", "Unit", "fun", "blame"]

identifier :: Parser String
identifier = lexeme $ do
  x <- letterChar <|> char '_'
  xs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = x : xs
  if T.pack name `elem` reserved
    then fail $ "keyword " ++ name ++ " cannot be used as identifier"
    else return name

-- =============================================================================
-- Term Parser
-- =============================================================================

parseTerm :: Text -> Either ParseError Term
parseTerm = parse (sc *> termParser <* eof) "<input>"

termParser :: Parser Term
termParser = choice
  [ try termApp
  , termAtom
  ]

termAtom :: Parser Term
termAtom = choice
  [ termLam
  , termIf
  , termLet
  , termCast
  , try termAscribe
  , termSucc
  , termPred
  , termIsZero
  , termTrue
  , termFalse
  , termZero
  , termUnit
  , termBlame
  , termVar
  , parens termParser
  ]

termVar :: Parser Term
termVar = Var <$> identifier

termLam :: Parser Term
termLam = do
  _ <- symbol "\\" <|> symbol "λ" <|> symbol "fun"
  x <- identifier
  _ <- symbol ":"
  ty <- typeParser
  _ <- symbol "."
  t <- termParser
  return $ Lam x ty t

termApp :: Parser Term
termApp = do
  t <- termAtom
  ts <- some termAtom
  return $ foldl App t ts

termIf :: Parser Term
termIf = do
  _ <- symbol "if"
  t1 <- termParser
  _ <- symbol "then"
  t2 <- termParser
  _ <- symbol "else"
  t3 <- termParser
  return $ TmIf t1 t2 t3

termLet :: Parser Term
termLet = do
  _ <- symbol "let"
  x <- identifier
  _ <- symbol "="
  t1 <- termParser
  _ <- symbol "in"
  t2 <- termParser
  return $ TmLet x t1 t2

termCast :: Parser Term
termCast = angles $ do
  ty1 <- typeParser
  _ <- symbol "=>"
  ty2 <- typeParser
  _ <- symbol ">"
  _ <- symbol "^"
  l <- identifier
  t <- termAtom
  return $ TmCast t ty1 ty2 l

termAscribe :: Parser Term
termAscribe = do
  t <- termVar <|> parens termParser
  _ <- symbol ":"
  ty <- typeParser
  return $ TmAscribe t ty

termSucc :: Parser Term
termSucc = TmSucc <$> (symbol "succ" *> termAtom)

termPred :: Parser Term
termPred = TmPred <$> (symbol "pred" *> termAtom)

termIsZero :: Parser Term
termIsZero = TmIsZero <$> (symbol "iszero" *> termAtom)

termTrue :: Parser Term
termTrue = TmTrue <$ symbol "true"

termFalse :: Parser Term
termFalse = TmFalse <$ symbol "false"

termZero :: Parser Term
termZero = TmZero <$ symbol "0"

termUnit :: Parser Term
termUnit = TmUnit <$ symbol "()"

termBlame :: Parser Term
termBlame = do
  _ <- symbol "blame"
  _ <- symbol "^"
  l <- identifier
  _ <- symbol ":"
  ty <- typeParser
  return $ TmBlame ty l

-- =============================================================================
-- Type Parser
-- =============================================================================

parseType :: Text -> Either ParseError Type
parseType = parse (sc *> typeParser <* eof) "<input>"

typeParser :: Parser Type
typeParser = try typeFun <|> typeAtom

typeAtom :: Parser Type
typeAtom = choice
  [ typeDyn
  , typeBool
  , typeNat
  , typeUnit
  , parens typeParser
  ]

typeFun :: Parser Type
typeFun = do
  ty1 <- typeAtom
  _ <- symbol "->"
  ty2 <- typeParser
  return $ TyFun ty1 ty2

typeDyn :: Parser Type
typeDyn = TyDyn <$ symbol "?"

typeBool :: Parser Type
typeBool = TyBool <$ symbol "Bool"

typeNat :: Parser Type
typeNat = TyNat <$ symbol "Nat"

typeUnit :: Parser Type
typeUnit = TyUnit <$ symbol "Unit"
