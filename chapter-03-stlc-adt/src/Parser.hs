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
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

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
typeParser = makeTypeExpr
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

    makeTypeExpr = do
      t <- prodType
      rest t

    prodType = do
      t <- typeAtom
      ts <- many (symbol "*" *> typeAtom)
      return $ foldl TyProd t ts

    rest t = do
      void (symbol "->")
      t' <- typeParser
      return (TyArr t t')
      <|> return t

    recordType = do
      void (symbol "{")
      fields <- ((,) <$> labelName <*> (symbol ":" *> typeParser)) `sepBy` symbol ","
      void (symbol "}")
      ensureUniqueLabels (map fst fields)
      return $ TyRecord (Map.fromList fields)

    variantType = do
      void (symbol "<")
      fields <- ((,) <$> labelName <*> (symbol ":" *> typeParser)) `sepBy` symbol ","
      void (symbol ">")
      ensureUniqueLabels (map fst fields)
      return $ TyVariant (Map.fromList fields)

-- Term parser
term :: Parser Term
term = choice [ifThenElse, matchExpr, caseExpr, consExpr]

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
  void (symbol ":")
  ty <- typeParser
  void (symbol "." <|> symbol "->")
  body <- term
  return $ Lam x ty body

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- Booleans
tmTrue :: Parser Term
tmTrue = TmTrue <$ symbol "true"

tmFalse :: Parser Term
tmFalse = TmFalse <$ symbol "false"

ifThenElse :: Parser Term
ifThenElse = do
  void (symbol "if")
  t1 <- term
  void (symbol "then")
  t2 <- term
  void (symbol "else")
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
  void (symbol ",")
  t2 <- term `sepBy1` symbol ","
  return $ foldl TmPair t1 t2

tmFst :: Parser Term
tmFst = symbol "fst" >> TmFst <$> atom

tmSnd :: Parser Term
tmSnd = symbol "snd" >> TmSnd <$> atom

-- Sums
tmInl :: Parser Term
tmInl = do
  void (symbol "inl")
  void (symbol "[")
  ty <- typeParser
  void (symbol "]")
  TmInl ty <$> atom

tmInr :: Parser Term
tmInr = do
  void (symbol "inr")
  void (symbol "[")
  ty <- typeParser
  void (symbol "]")
  TmInr ty <$> atom

caseExpr :: Parser Term
caseExpr = do
  void (symbol "case")
  t <- term
  void (symbol "of")
  try (sumCase t) <|> matchCase t
  where
    sumCase t = do
      void (symbol "inl")
      x1 <- varName
      void (symbol "=>")
      t1 <- term
      void (symbol "|")
      void (symbol "inr")
      x2 <- varName
      void (symbol "=>")
      t2 <- term
      return $ TmCase t x1 t1 x2 t2

    matchCase t = do
      cases <- patternCase `sepBy1` symbol "|"
      return $ TmMatch t cases

-- Records
record :: Parser Term
record = do
  void (symbol "{")
  fields <- ((,) <$> labelName <*> (symbol "=" *> term)) `sepBy` symbol ","
  void (symbol "}")
  ensureUniqueLabels (map fst fields)
  return $ TmRecord (Map.fromList fields)

-- Variants
variant :: Parser Term
variant = do
  void (symbol "<")
  lbl <- labelName
  void (symbol "=")
  t <- term
  void (symbol ">")
  void (symbol "as")
  ty <- typeParser
  return $ TmTag lbl t ty

-- Lists
tmNil :: Parser Term
tmNil = do
  void (symbol "[")
  void (symbol "]")
  void (symbol ":")
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
  void (symbol "match")
  t <- term
  void (symbol "with")
  cases <- patternCase `sepBy1` symbol "|"
  return $ TmMatch t cases

patternCase :: Parser (Pattern, Term)
patternCase = do
  pat <- pattern
  void (symbol "=>")
  t <- term
  return (pat, t)

pattern :: Parser Pattern
pattern = patternCons

patternCons :: Parser Pattern
patternCons = do
  p <- patternNoCons
  rest p
  where
    rest p =
      (symbol "::" >> (PatCons p <$> patternCons))
        <|> return p

patternNoCons :: Parser Pattern
patternNoCons = choice
  [ PatSucc <$> (symbol "succ" *> patternNoCons)
  , PatInl <$> (symbol "inl" *> patternNoCons)
  , PatInr <$> (symbol "inr" *> patternNoCons)
  , variantPattern
  , patternAtom
  ]

patternAtom :: Parser Pattern
patternAtom = choice
  [ PatWild <$ symbol "_"
  , PatUnit <$ symbol "()"
  , PatTrue <$ symbol "true"
  , PatFalse <$ symbol "false"
  , PatZero <$ symbol "0"
  , PatNil <$ (symbol "[" >> symbol "]")
  , try $ parens pairPattern
  , parens pattern
  , PatVar <$> varName
  ]

pairPattern :: Parser Pattern
pairPattern = do
  p1 <- pattern
  void (symbol ",")
  ps <- pattern `sepBy1` symbol ","
  return $ foldl PatPair p1 ps

variantPattern :: Parser Pattern
variantPattern = do
  void (symbol "<")
  lbl <- labelName
  void (symbol "=")
  pat <- pattern
  void (symbol ">")
  return $ PatVariant lbl pat

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

ensureUniqueLabels :: [Label] -> Parser ()
ensureUniqueLabels labels =
  case firstDuplicate labels of
    Just dup -> fail ("duplicate label: " ++ dup)
    Nothing -> return ()

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (x:xs)
      | Set.member x seen = Just x
      | otherwise = go (Set.insert x seen) xs
