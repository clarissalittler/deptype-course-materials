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
keywords = ["if", "then", "else", "true", "false", "let", "in",
            "succ", "pred", "iszero", "fst", "snd", "isnil", "head", "tail"]

varName :: Parser Var
varName = lexeme $ try $ do
  c <- lowerChar
  cs <- many alphaNumChar
  let name = c : cs
  if name `elem` keywords
    then fail $ "keyword " ++ name ++ " cannot be used as variable"
    else return name

typeParser :: Parser Type
typeParser = makeTypeExpr
  where
    typeAtom = choice
      [ TyBool <$ symbol "Bool"
      , TyNat <$ symbol "Nat"
      , try $ TyList <$> (symbol "List" *> typeAtom)
      , parens typeParser
      ]
    makeTypeExpr = do
      t <- prodType
      rest t
    prodType = do
      t <- typeAtom
      ts <- many (symbol "*" *> typeAtom)
      return $ foldl TyProd t ts
    rest t =
      (TyArr t <$> (void (symbol "->") *> typeParser))
        <|> return t

term :: Parser Term
term = choice [ifExpr, letExpr, consExpr]

consExpr :: Parser Term
consExpr = do
  t <- application
  rest t
  where
    rest t =
      (symbol "::" >> (TmCons t <$> consExpr))
        <|> return t

application :: Parser Term
application = do
  t <- atom
  ts <- many atom
  return $ foldl App t ts

atom :: Parser Term
atom = choice
  [ try pair
  , parens term
  , lambda
  , tmTrue
  , tmFalse
  , tmZero
  , tmSucc
  , tmPred
  , tmIsZero
  , tmFst
  , tmSnd
  , tmNil
  , tmIsNil
  , tmHead
  , tmTail
  , variable
  ]

variable :: Parser Term
variable = Var <$> varName

-- NO TYPE ANNOTATION! This is Hindley-Milner!
lambda :: Parser Term
lambda = do
  void (symbol "λ" <|> symbol "\\")
  x <- varName
  void (symbol "." <|> symbol "->")
  body <- term
  return $ Lam x body

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

tmTrue :: Parser Term
tmTrue = TmTrue <$ symbol "true"

tmFalse :: Parser Term
tmFalse = TmFalse <$ symbol "false"

ifExpr :: Parser Term
ifExpr = do
  void (symbol "if")
  t1 <- term
  void (symbol "then")
  t2 <- term
  void (symbol "else")
  t3 <- term
  return $ TmIf t1 t2 t3

letExpr :: Parser Term
letExpr = do
  void (symbol "let")
  x <- varName
  void (symbol "=")
  t1 <- term
  void (symbol "in")
  t2 <- term
  return $ Let x t1 t2

tmZero :: Parser Term
tmZero = TmZero <$ symbol "0"

tmSucc :: Parser Term
tmSucc = symbol "succ" >> TmSucc <$> atom

tmPred :: Parser Term
tmPred = symbol "pred" >> TmPred <$> atom

tmIsZero :: Parser Term
tmIsZero = symbol "iszero" >> TmIsZero <$> atom

pair :: Parser Term
pair = parens $ do
  t1 <- term
  void (symbol ",")
  t2 <- term
  return $ TmPair t1 t2

tmFst :: Parser Term
tmFst = symbol "fst" >> TmFst <$> atom

tmSnd :: Parser Term
tmSnd = symbol "snd" >> TmSnd <$> atom

tmNil :: Parser Term
tmNil = TmNil <$ (symbol "[" >> symbol "]")

tmIsNil :: Parser Term
tmIsNil = symbol "isnil" >> TmIsNil <$> atom

tmHead :: Parser Term
tmHead = symbol "head" >> TmHead <$> atom

tmTail :: Parser Term
tmTail = symbol "tail" >> TmTail <$> atom

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
