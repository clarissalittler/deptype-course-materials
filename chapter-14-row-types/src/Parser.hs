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
import qualified Data.Map as Map
import Text.Megaparsec hiding (ParseError)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text
type ParseError = ParseErrorBundle Text Void

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

angles :: Parser a -> Parser a
angles = between (symbol "<") (symbol ">")

reserved :: [Text]
reserved = ["true", "false", "if", "then", "else", "succ", "pred", "iszero",
            "let", "in", "Bool", "Nat", "Unit", "fun", "case", "of", "forall"]

identifier :: Parser String
identifier = lexeme $ do
  x <- letterChar <|> char '_'
  xs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = x : xs
  if T.pack name `elem` reserved
    then fail $ "keyword " ++ name ++ " cannot be used as identifier"
    else return name

labelP :: Parser Label
labelP = identifier

parseTerm :: Text -> Either ParseError Term
parseTerm = parse (sc *> termParser <* eof) "<input>"

termParser :: Parser Term
termParser = choice [try termApp, termAtom]

termAtom :: Parser Term
termAtom = choice
  [ termLam, termIf, termLet, termCase
  , termRecord, termVariant
  , termSucc, termPred, termIsZero
  , termTrue, termFalse, termZero, termUnit
  , try termProj, termVar
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
termIf = TmIf <$> (symbol "if" *> termParser)
              <*> (symbol "then" *> termParser)
              <*> (symbol "else" *> termParser)

termLet :: Parser Term
termLet = TmLet <$> (symbol "let" *> identifier)
                <*> (symbol "=" *> termParser)
                <*> (symbol "in" *> termParser)

termRecord :: Parser Term
termRecord = braces $ do
  fields <- fieldBinding `sepBy` symbol ","
  return $ TmRecord (Map.fromList fields)

fieldBinding :: Parser (Label, Term)
fieldBinding = (,) <$> labelP <*> (symbol "=" *> termParser)

termProj :: Parser Term
termProj = do
  t <- termVar <|> parens termParser
  _ <- symbol "."
  l <- labelP
  return $ TmProj t l

termVariant :: Parser Term
termVariant = do
  (l, t) <- angles $ (,) <$> labelP <*> (symbol "=" *> termParser)
  _ <- symbol ":"
  ty <- typeParser
  return $ TmVariant l t ty

termCase :: Parser Term
termCase = do
  _ <- symbol "case"
  t <- termParser
  _ <- symbol "of"
  cases <- caseClause `sepBy1` symbol "|"
  return $ TmCase t cases

caseClause :: Parser (Label, Var, Term)
caseClause = do
  _ <- symbol "<"
  l <- labelP
  _ <- symbol "="
  x <- identifier
  _ <- symbol ">"
  _ <- symbol "->"
  body <- termParser
  return (l, x, body)

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

parseType :: Text -> Either ParseError Type
parseType = parse (sc *> typeParser <* eof) "<input>"

typeParser :: Parser Type
typeParser = try typeFun <|> try typeForallRow <|> typeAtom

typeAtom :: Parser Type
typeAtom = choice
  [ typeBool, typeNat, typeUnit
  , typeRecord, typeVariant
  , parens typeParser
  ]

typeFun :: Parser Type
typeFun = do
  ty1 <- typeAtom
  _ <- symbol "->"
  ty2 <- typeParser
  return $ TyFun ty1 ty2

typeForallRow :: Parser Type
typeForallRow = do
  _ <- symbol "forall" <|> symbol "∀"
  v <- identifier
  _ <- symbol "."
  ty <- typeParser
  return $ TyForallRow v ty

typeBool :: Parser Type
typeBool = TyBool <$ symbol "Bool"

typeNat :: Parser Type
typeNat = TyNat <$ symbol "Nat"

typeUnit :: Parser Type
typeUnit = TyUnit <$ symbol "Unit"

typeRecord :: Parser Type
typeRecord = TyRecord <$> braces rowParser

typeVariant :: Parser Type
typeVariant = TyVariant <$> angles rowParser

rowParser :: Parser Row
rowParser = do
  fields <- rowField `sepBy` symbol ","
  mvar <- optional (symbol "|" *> identifier)
  let base = maybe RowEmpty RowVar mvar
  return $ foldr (\(l, ty) r -> RowExtend l ty r) base fields

rowField :: Parser (Label, Type)
rowField = (,) <$> labelP <*> (symbol ":" *> typeParser)
