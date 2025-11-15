{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( parseTerm
  , parseType
  , Parser
  ) where

import Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text (Text)
import Data.Void (Void)
import Control.Monad (void)

type Parser = Parsec Void Text

-- | Space consumer
sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

-- | Lexeme parser
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- | Symbol parser
symbol :: Text -> Parser Text
symbol = L.symbol sc

-- | Reserved keywords that cannot be used as variable names
keywords :: [String]
keywords = ["if", "then", "else", "true", "false", "succ", "pred", "iszero"]

-- | Parse a variable name (not a keyword)
varName :: Parser Var
varName = lexeme $ try $ do
  c <- lowerChar
  cs <- many alphaNumChar
  let name = c : cs
  if name `elem` keywords
    then fail $ "keyword " ++ name ++ " cannot be used as a variable name"
    else return name

-- | Lambda symbol
lambdaSymbol :: Parser ()
lambdaSymbol = void (symbol "λ" <|> symbol "\\")

-- | Parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Parse a type
typeParser :: Parser Type
typeParser = makeTypeExpr typeAtom
  where
    typeAtom = choice
      [ TyBool <$ symbol "Bool"
      , TyNat <$ symbol "Nat"
      , parens typeParser
      ]

    makeTypeExpr :: Parser Type -> Parser Type
    makeTypeExpr atom = do
      t <- atom
      rest t

    rest :: Type -> Parser Type
    rest t = do
      symbol "->"
      t' <- typeParser
      return (TyArr t t')
      <|> return t

-- | Parse a term
term :: Parser Term
term = choice
  [ ifThenElse  -- Parse if-then-else at term level
  , application
  ]

-- | Parse application (handles left-associativity)
application :: Parser Term
application = do
  t <- atom
  ts <- many atom
  return $ foldl App t ts

-- | Parse an atomic term
atom :: Parser Term
atom = choice
  [ parens term
  , lambda
  , tmTrue
  , tmFalse
  , tmZero
  , tmSucc
  , tmPred
  , tmIsZero
  , variable
  ]

-- | Parse a variable
variable :: Parser Term
variable = Var <$> varName

-- | Parse a lambda abstraction
lambda :: Parser Term
lambda = do
  lambdaSymbol
  x <- varName
  symbol ":"
  ty <- typeParser
  void (symbol "." <|> symbol "->")
  body <- term
  return $ Lam x ty body

-- | Parse if-then-else
ifThenElse :: Parser Term
ifThenElse = do
  symbol "if"
  t1 <- application  -- Use application instead of term to avoid infinite recursion
  symbol "then"
  t2 <- application
  symbol "else"
  t3 <- term  -- Last branch can be any term
  return $ TmIf t1 t2 t3

-- | Parse true
tmTrue :: Parser Term
tmTrue = TmTrue <$ symbol "true"

-- | Parse false
tmFalse :: Parser Term
tmFalse = TmFalse <$ symbol "false"

-- | Parse zero
tmZero :: Parser Term
tmZero = TmZero <$ symbol "0"

-- | Parse successor
tmSucc :: Parser Term
tmSucc = do
  symbol "succ"
  TmSucc <$> atom

-- | Parse predecessor
tmPred :: Parser Term
tmPred = do
  symbol "pred"
  TmPred <$> atom

-- | Parse iszero
tmIsZero :: Parser Term
tmIsZero = do
  symbol "iszero"
  TmIsZero <$> atom

-- | Parse a term from text
parseTerm :: Text -> Either String Term
parseTerm input =
  case runParser (sc *> term <* eof) "" input of
    Left err -> Left (errorBundlePretty err)
    Right t -> Right t

-- | Parse a type from text
parseType :: Text -> Either String Type
parseType input =
  case runParser (sc *> typeParser <* eof) "" input of
    Left err -> Left (errorBundlePretty err)
    Right t -> Right t
