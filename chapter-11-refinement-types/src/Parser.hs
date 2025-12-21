{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( -- * Parsing
    parseTerm
  , parseType
  , parsePred
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
import Control.Monad.Combinators.Expr

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

reserved :: [Text]
reserved = ["true", "false", "if", "then", "else", "succ", "pred", "iszero",
            "let", "in", "Bool", "Nat", "Unit", "fun", "forall"]

identifier :: Parser String
identifier = lexeme $ do
  x <- letterChar <|> char '_'
  xs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = x : xs
  if T.pack name `elem` reserved
    then fail $ "keyword " ++ name ++ " cannot be used as identifier"
    else return name

integer :: Parser Int
integer = lexeme L.decimal

-- =============================================================================
-- Term Parser
-- =============================================================================

parseTerm :: Text -> Either ParseError Term
parseTerm = parse (sc *> termParser <* eof) "<input>"

termParser :: Parser Term
termParser = makeExprParser termAtom termOps

termOps :: [[Operator Parser Term]]
termOps =
  [ [ InfixL (TmArith Add <$ symbol "+")
    , InfixL (TmArith Sub <$ symbol "-")
    ]
  ]

termAtom :: Parser Term
termAtom = choice
  [ try termAscribe
  , try termApp
  , termSimple
  ]

termSimple :: Parser Term
termSimple = choice
  [ termLam
  , termIf
  , termLet
  , termSucc
  , termPred
  , termIsZero
  , termTrue
  , termFalse
  , termZero
  , termNat
  , termUnit
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
  t <- termSimple
  ts <- some termSimple
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

termSucc :: Parser Term
termSucc = TmSucc <$> (symbol "succ" *> termSimple)

termPred :: Parser Term
termPred = TmPred <$> (symbol "pred" *> termSimple)

termIsZero :: Parser Term
termIsZero = TmIsZero <$> (symbol "iszero" *> termSimple)

termTrue :: Parser Term
termTrue = TmTrue <$ symbol "true"

termFalse :: Parser Term
termFalse = TmFalse <$ symbol "false"

termZero :: Parser Term
termZero = TmZero <$ symbol "0"

termNat :: Parser Term
termNat = do
  n <- integer
  return $ iterate TmSucc TmZero !! n

termUnit :: Parser Term
termUnit = TmUnit <$ symbol "()"

termAscribe :: Parser Term
termAscribe = do
  t <- try (termSimple <* symbol ":")
  ty <- typeParser
  return $ TmAscribe t ty

-- =============================================================================
-- Type Parser
-- =============================================================================

parseType :: Text -> Either ParseError Type
parseType = parse (sc *> typeParser <* eof) "<input>"

typeParser :: Parser Type
typeParser = try typeFun <|> typeAtom

typeAtom :: Parser Type
typeAtom = choice
  [ try typeRefine
  , typeBool
  , typeNat
  , typeUnit
  , parens typeParser
  ]

typeFun :: Parser Type
typeFun = do
  -- (x: T1) -> T2  or  T1 -> T2
  (x, ty1) <- try dependentArg <|> simpleArg
  _ <- symbol "->"
  ty2 <- typeParser
  return $ TyFun x ty1 ty2
  where
    dependentArg = parens $ do
      x <- identifier
      _ <- symbol ":"
      ty <- typeParser
      return (x, ty)
    simpleArg = do
      ty <- typeAtom
      return ("_", ty)

typeBool :: Parser Type
typeBool = TyBase TyBool <$ symbol "Bool"

typeNat :: Parser Type
typeNat = TyBase TyNat <$ symbol "Nat"

typeUnit :: Parser Type
typeUnit = TyBase TyUnit <$ symbol "Unit"

-- | Parse refinement type: {x: T | φ}
typeRefine :: Parser Type
typeRefine = braces $ do
  x <- identifier
  _ <- symbol ":"
  ty <- typeParser
  _ <- symbol "|"
  p <- predParser
  return $ TyRefine x ty p

-- =============================================================================
-- Predicate Parser
-- =============================================================================

parsePred :: Text -> Either ParseError Pred
parsePred = parse (sc *> predParser <* eof) "<input>"

predParser :: Parser Pred
predParser = makeExprParser predAtom predOps

predOps :: [[Operator Parser Pred]]
predOps =
  [ [ Prefix (PNot <$ symbol "!") ]
  , [ InfixL (PAnd <$ symbol "&&")
    , InfixL (PAnd <$ symbol "∧")
    ]
  , [ InfixL (POr <$ symbol "||")
    , InfixL (POr <$ symbol "∨")
    ]
  , [ InfixR (PImpl <$ symbol "=>")
    , InfixR (PImpl <$ symbol "⇒")
    ]
  ]

predAtom :: Parser Pred
predAtom = choice
  [ PTrue <$ symbol "true"
  , PFalse <$ symbol "false"
  , try predComp
  , PVar <$> identifier
  , parens predParser
  ]

predComp :: Parser Pred
predComp = do
  a1 <- arithParser
  op <- compOp
  a2 <- arithParser
  return $ PComp op a1 a2

compOp :: Parser CompOp
compOp = choice
  [ OpEq <$ (symbol "==" <|> symbol "=")
  , OpNeq <$ (symbol "!=" <|> symbol "≠")
  , OpLe <$ (symbol "<=" <|> symbol "≤")
  , OpGe <$ (symbol ">=" <|> symbol "≥")
  , OpLt <$ symbol "<"
  , OpGt <$ symbol ">"
  ]

arithParser :: Parser PArith
arithParser = makeExprParser arithAtom arithOps

arithOps :: [[Operator Parser PArith]]
arithOps =
  [ [ InfixL (PAAdd <$ symbol "+")
    , InfixL (PASub <$ symbol "-")
    ]
  ]

arithAtom :: Parser PArith
arithAtom = choice
  [ PALit <$> integer
  , PAVar <$> identifier
  , parens arithParser
  ]
