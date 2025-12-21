{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( -- * Parsing
    parseTerm
  , parseType
  , parseEffectRow
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

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

reserved :: [Text]
reserved = ["true", "false", "if", "then", "else", "succ", "pred", "iszero",
            "let", "in", "Bool", "Nat", "Unit", "fun", "perform", "handle",
            "with", "return", "handler", "forall"]

identifier :: Parser String
identifier = lexeme $ do
  x <- letterChar <|> char '_'
  xs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = x : xs
  if T.pack name `elem` reserved
    then fail $ "keyword " ++ name ++ " cannot be used as identifier"
    else return name

-- | Parse an effect label (uppercase identifier)
effectLabel :: Parser EffectLabel
effectLabel = lexeme $ do
  x <- upperChar
  xs <- many alphaNumChar
  return (x : xs)

-- =============================================================================
-- Term Parser
-- =============================================================================

parseTerm :: Text -> Either ParseError Term
parseTerm = parse (sc *> termParser <* eof) "<input>"

termParser :: Parser Term
termParser = choice
  [ try termHandle
  , try termApp
  , termAtom
  ]

termAtom :: Parser Term
termAtom = choice
  [ termLam
  , termEffAbs
  , termIf
  , termLet
  , termPerform
  , termReturn
  , termSucc
  , termPred
  , termIsZero
  , termTrue
  , termFalse
  , termZero
  , termUnit
  , try termEffApp
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

termEffAbs :: Parser Term
termEffAbs = do
  _ <- symbol "Λ" <|> symbol "/\\"
  v <- identifier
  _ <- symbol "."
  t <- termParser
  return $ TmEffAbs v t

termEffApp :: Parser Term
termEffApp = do
  t <- termVar <|> parens termParser
  effs <- some (brackets effectRowParser)
  return $ foldl TmEffApp t effs

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

termPerform :: Parser Term
termPerform = do
  _ <- symbol "perform"
  eff <- effectLabel
  _ <- symbol "."
  op <- identifier
  t <- termAtom
  return $ TmPerform eff op t

termHandle :: Parser Term
termHandle = do
  _ <- symbol "handle"
  t <- termAtom
  _ <- symbol "with"
  h <- handlerParser
  return $ TmHandle t h

termReturn :: Parser Term
termReturn = do
  _ <- symbol "return"
  t <- termAtom
  return $ TmReturn t

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

-- =============================================================================
-- Handler Parser
-- =============================================================================

handlerParser :: Parser Handler
handlerParser = braces $ do
  eff <- effectLabel
  _ <- symbol ":"
  retClause <- returnClause
  opClauses <- many opClause
  return $ Handler eff retClause opClauses

returnClause :: Parser (Var, Term)
returnClause = do
  _ <- symbol "return"
  x <- identifier
  _ <- symbol "->"
  body <- termParser
  optional (symbol ";")
  return (x, body)

opClause :: Parser (String, Var, Var, Term)
opClause = do
  op <- identifier
  param <- identifier
  cont <- identifier
  _ <- symbol "->"
  body <- termParser
  optional (symbol ";")
  return (op, param, cont, body)

-- =============================================================================
-- Type Parser
-- =============================================================================

parseType :: Text -> Either ParseError Type
parseType = parse (sc *> typeParser <* eof) "<input>"

typeParser :: Parser Type
typeParser = try typeFun <|> try typeForallEff <|> typeAtom

typeAtom :: Parser Type
typeAtom = choice
  [ typeBool
  , typeNat
  , typeUnit
  , parens typeParser
  ]

typeFun :: Parser Type
typeFun = do
  ty1 <- typeAtom
  _ <- symbol "->"
  ty2 <- typeParser
  eff <- option EffEmpty (symbol "!" *> effectRowParser)
  return $ TyFun ty1 ty2 eff

typeForallEff :: Parser Type
typeForallEff = do
  _ <- symbol "forall" <|> symbol "∀"
  v <- identifier
  _ <- symbol "."
  ty <- typeParser
  return $ TyForallEff v ty

typeBool :: Parser Type
typeBool = TyBool <$ symbol "Bool"

typeNat :: Parser Type
typeNat = TyNat <$ symbol "Nat"

typeUnit :: Parser Type
typeUnit = TyUnit <$ symbol "Unit"

-- =============================================================================
-- Effect Row Parser
-- =============================================================================

parseEffectRow :: Text -> Either ParseError EffectRow
parseEffectRow = parse (sc *> effectRowParser <* eof) "<input>"

effectRowParser :: Parser EffectRow
effectRowParser = braces effectRowInner <|> pure EffEmpty

effectRowInner :: Parser EffectRow
effectRowInner = do
  labels <- effectLabel `sepBy` symbol ","
  mvar <- optional (symbol "|" *> identifier)
  let baseRow = case mvar of
        Nothing -> EffEmpty
        Just v -> EffVar v
  return $ foldr EffLabel baseRow labels
