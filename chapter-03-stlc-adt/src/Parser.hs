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
import qualified Data.Text as T
import Data.Void (Void)
import Control.Monad (void)
import qualified Data.Map.Strict as Map

type Parser = Parsec Void Text

-- Space consumer
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

-- Lexeme and symbol
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

-- Keywords
keywords :: [String]
keywords = ["if", "then", "else", "true", "false", "succ", "pred", "iszero",
            "fst", "snd", "inl", "inr", "case", "of", "as", "match", "with",
            "nil", "isnil", "head", "tail", "Bool", "Nat", "Unit", "List"]

-- Variable name
varName :: Parser Var
varName = lexeme $ try $ do
  c <- lowerChar
  cs <- many alphaNumChar
  let name = c : cs
  if name `elem` keywords
    then fail $ "keyword " ++ name ++ " cannot be used as variable"
    else return name

-- Label (for records/variants)
labelName :: Parser Label
labelName = varName

-- Type parser
typeParser :: Parser Type
typeParser = makeTypeExpr typeAtom
  where
    typeAtom = choice
      [ TyBool <$ symbol "Bool"
      , TyNat <$ symbol "Nat"
      , TyUnit <$ symbol "Unit"
      , try $ TyList <$> (symbol "List" *> typeAtom)
      , parens typeParser
      , recordType
      , variantType
      ]

    makeTypeExpr atom = do
      t <- prodType atom
      rest t

    prodType atom = do
      t <- atom
      ts <- many (symbol "*" *> atom)
      return $ foldl TyProd t ts

    rest t = do
      symbol "->"
      t' <- typeParser
      return (TyArr t t')
      <|> return t

    recordType = do
      symbol "{"
      fields <- ((,) <$> labelName <*> (symbol ":" *> typeParser)) `sepBy` symbol ","
      symbol "}"
      return $ TyRecord (Map.fromList fields)

    variantType = do
      symbol "<"
      fields <- ((,) <$> labelName <*> (symbol ":" *> typeParser)) `sepBy` symbol ","
      symbol ">"
      return $ TyVariant (Map.fromList fields)

-- Term parser
term :: Parser Term
term = choice [ifThenElse, matchExpr, caseExpr, application]

application :: Parser Term
application = do
  t <- atom
  ts <- many atom
  return $ foldl App t ts

atom :: Parser Term
atom = choice
  [ try pair  -- Try pair before parens term
  , try record
  , try variant
  , parens term
  , lambda
  , tmUnit
  , tmTrue
  , tmFalse
  , tmZero
  , tmSucc
  , tmPred
  , tmIsZero
  , tmFst
  , tmSnd
  , tmInl
  , tmInr
  , tmNil
  , tmIsNil
  , tmHead
  , tmTail
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

lambdaSymbol :: Parser ()
lambdaSymbol = void (symbol "λ" <|> symbol "\\")

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- Booleans
tmTrue :: Parser Term
tmTrue = TmTrue <$ symbol "true"

tmFalse :: Parser Term
tmFalse = TmFalse <$ symbol "false"

ifThenElse :: Parser Term
ifThenElse = do
  symbol "if"
  t1 <- application
  symbol "then"
  t2 <- application
  symbol "else"
  t3 <- term
  return $ TmIf t1 t2 t3

-- Natural numbers
tmZero :: Parser Term
tmZero = TmZero <$ symbol "0"

tmSucc :: Parser Term
tmSucc = symbol "succ" >> TmSucc <$> atom

tmPred :: Parser Term
tmPred = symbol "pred" >> TmPred <$> atom

tmIsZero :: Parser Term
tmIsZero = symbol "iszero" >> TmIsZero <$> atom

-- Unit
tmUnit :: Parser Term
tmUnit = TmUnit <$ symbol "()"

-- Products (pairs)
pair :: Parser Term
pair = parens $ do
  t1 <- term
  symbol ","
  t2 <- term `sepBy1` symbol ","
  return $ foldl TmPair t1 t2

tmFst :: Parser Term
tmFst = symbol "fst" >> TmFst <$> atom

tmSnd :: Parser Term
tmSnd = symbol "snd" >> TmSnd <$> atom

-- Sums
tmInl :: Parser Term
tmInl = do
  symbol "inl"
  symbol "["
  ty <- typeParser
  symbol "]"
  TmInl ty <$> atom

tmInr :: Parser Term
tmInr = do
  symbol "inr"
  symbol "["
  ty <- typeParser
  symbol "]"
  TmInr ty <$> atom

caseExpr :: Parser Term
caseExpr = do
  symbol "case"
  t <- application
  symbol "of"
  symbol "inl"
  x1 <- varName
  symbol "=>"
  t1 <- term
  symbol "|"
  symbol "inr"
  x2 <- varName
  symbol "=>"
  t2 <- term
  return $ TmCase t x1 t1 x2 t2

-- Records
record :: Parser Term
record = do
  symbol "{"
  fields <- ((,) <$> labelName <*> (symbol "=" *> term)) `sepBy` symbol ","
  symbol "}"
  return $ TmRecord (Map.fromList fields)

-- Variants
variant :: Parser Term
variant = do
  symbol "<"
  label <- labelName
  symbol "="
  t <- term
  symbol ">"
  symbol "as"
  ty <- typeParser
  return $ TmTag label t ty

-- Lists
tmNil :: Parser Term
tmNil = do
  symbol "["
  symbol "]"
  symbol ":"
  TmNil <$> typeParser

tmIsNil :: Parser Term
tmIsNil = symbol "isnil" >> TmIsNil <$> atom

tmHead :: Parser Term
tmHead = symbol "head" >> TmHead <$> atom

tmTail :: Parser Term
tmTail = symbol "tail" >> TmTail <$> atom

-- Pattern matching
matchExpr :: Parser Term
matchExpr = do
  symbol "match"
  t <- application
  symbol "with"
  cases <- patternCase `sepBy1` symbol "|"
  return $ TmMatch t cases

patternCase :: Parser (Pattern, Term)
patternCase = do
  pat <- pattern'
  symbol "=>"
  t <- term
  return (pat, t)

pattern' :: Parser Pattern
pattern' = choice
  [ PatWild <$ symbol "_"
  , PatUnit <$ symbol "()"
  , PatTrue <$ symbol "true"
  , PatFalse <$ symbol "false"
  , PatZero <$ symbol "0"
  , PatNil <$ (symbol "[" >> symbol "]")
  , try $ parens pairPattern
  , PatVar <$> varName
  ]

pairPattern :: Parser Pattern
pairPattern = do
  p1 <- pattern'
  symbol ","
  p2 <- pattern'
  return $ PatPair p1 p2

-- Parse functions
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
