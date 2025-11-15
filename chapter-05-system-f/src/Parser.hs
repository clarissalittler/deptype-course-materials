{-# LANGUAGE OverloadedStrings #-}

module Parser (parseTerm, parseType) where

import Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text (Text)
import Data.Void (Void)
import Control.Monad (void)

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

keywords :: [String]
keywords = ["if", "then", "else", "true", "false", "succ", "pred", "iszero",
            "Bool", "Nat", "forall"]

varName :: Parser Var
varName = lexeme $ try $ do
  c <- lowerChar
  cs <- many alphaNumChar
  let name = c : cs
  if name `elem` keywords
    then fail $ "keyword " ++ name ++ " cannot be used"
    else return name

tyVarName :: Parser TyVar
tyVarName = lexeme $ do
  c <- upperChar
  cs <- many alphaNumChar
  return (c : cs)

-- Type parser
typeParser :: Parser Type
typeParser = makeTypeExpr typeAtom
  where
    typeAtom = choice
      [ TyBool <$ symbol "Bool"
      , TyNat <$ symbol "Nat"
      , forallType
      , TyVar <$> tyVarName
      , parens typeParser
      ]
    makeTypeExpr atom = do
      t <- atom
      rest t
    rest t = do
      symbol "->"
      t' <- typeParser
      return (TyArr t t')
      <|> return t
    forallType = do
      symbol "forall" <|> symbol "∀"
      a <- tyVarName
      symbol "."
      ty <- typeParser
      return $ TyForall a ty

-- Term parser
term :: Parser Term
term = choice [ifExpr, application]

application :: Parser Term
application = do
  t <- atom
  ts <- many (Left <$> atom <|> Right <$> typeArg)
  return $ foldl applyArg t ts
  where
    applyArg t (Left t') = App t t'
    applyArg t (Right ty) = TyApp t ty

typeArg :: Parser Type
typeArg = between (symbol "[") (symbol "]") typeParser

atom :: Parser Term
atom = choice
  [ parens term
  , lambda
  , tyAbsExpr
  , tmTrue
  , tmFalse
  , tmZero
  , tmSucc
  , tmPred
  , tmIsZero
  , variable
  ]

variable :: Parser Term
variable = Var <$> varName

lambda :: Parser Term
lambda = do
  void (symbol "λ" <|> symbol "\\")
  x <- varName
  symbol ":"
  ty <- typeParser
  void (symbol "." <|> symbol "->")
  body <- term
  return $ Lam x ty body

tyAbsExpr :: Parser Term
tyAbsExpr = do
  void (symbol "Λ" <|> symbol "/\\")
  a <- tyVarName
  void (symbol "." <|> symbol "->")
  body <- term
  return $ TyAbs a body

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

tmTrue :: Parser Term
tmTrue = TmTrue <$ symbol "true"

tmFalse :: Parser Term
tmFalse = TmFalse <$ symbol "false"

ifExpr :: Parser Term
ifExpr = do
  symbol "if"
  t1 <- application
  symbol "then"
  t2 <- application
  symbol "else"
  t3 <- term
  return $ TmIf t1 t2 t3

tmZero :: Parser Term
tmZero = TmZero <$ symbol "0"

tmSucc :: Parser Term
tmSucc = symbol "succ" >> TmSucc <$> atom

tmPred :: Parser Term
tmPred = symbol "pred" >> TmPred <$> atom

tmIsZero :: Parser Term
tmIsZero = symbol "iszero" >> TmIsZero <$> atom

parseTerm :: Text -> Either String Term
parseTerm input =
  case runParser (sc *> term <* eof) "" input of
    Left err -> Left (errorBundlePretty err)
    Right t -> Right t

parseType :: Text -> Either String Type
parseType input =
  case runParser (sc *> typeParser <* eof) "" input of
    Left err -> Left (errorBundlePretty err)
    Right t -> Right t
