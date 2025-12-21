{-# LANGUAGE OverloadedStrings #-}

module Parser (parseTerm, parseType) where

import Syntax
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Data.Void
import Data.Text (Text)

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

identifier :: Parser String
identifier = lexeme $ do
  c <- letterChar <|> char '_'
  cs <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = c : cs
  if name `elem` reserved then fail $ name ++ " is reserved" else return name
  where
    reserved = ["true", "false", "if", "then", "else", "succ", "pred", "iszero",
                "unit", "fst", "snd", "inl", "inr", "case", "of", "let", "in",
                "Bool", "Nat", "Unit", "Void", "Type", "Id",
                "refl", "J", "sym", "trans", "ap", "transport", "absurd"]

-- | Parse types
parseType :: Text -> Either String Type
parseType input = case parse (sc *> typeP <* eof) "" input of
  Left err -> Left $ errorBundlePretty err
  Right ty -> Right ty

typeP :: Parser Type
typeP = makeExprParser typeAtom typeOps
  where
    typeOps =
      [ [InfixR (TyFun <$ symbol "->")]
      , [InfixL (TyProd <$ symbol "*")]
      , [InfixL (TySum <$ symbol "+")]
      ]

typeAtom :: Parser Type
typeAtom = choice
  [ TyBool <$ symbol "Bool"
  , TyNat <$ symbol "Nat"
  , TyUnit <$ symbol "Unit"
  , TyVoid <$ symbol "Void"
  , TyUniverse <$ symbol "Type"
  , idType
  , TyVar <$> identifier
  , parens typeP
  ]

-- Id A a b
idType :: Parser Type
idType = do
  _ <- symbol "Id"
  ty <- typeAtom
  a <- termAtom
  b <- termAtom
  return $ TyId ty a b

-- | Parse terms
parseTerm :: Text -> Either String Term
parseTerm input = case parse (sc *> termP <* eof) "" input of
  Left err -> Left $ errorBundlePretty err
  Right t -> Right t

termP :: Parser Term
termP = makeExprParser termAtom termOps
  where
    termOps = [[InfixL (App <$ space1)]]

termAtom :: Parser Term
termAtom = choice
  [ TmTrue <$ symbol "true"
  , TmFalse <$ symbol "false"
  , TmUnit <$ symbol "unit"
  , TmZero <$ symbol "0"
  , ifTerm
  , succTerm
  , predTerm
  , isZeroTerm
  , pairTerm
  , fstTerm
  , sndTerm
  , inlTerm
  , inrTerm
  , caseTerm
  , letTerm
  , absurdTerm
  , reflTerm
  , jTerm
  , symTerm
  , transportTerm  -- Must come before transTerm (trans is prefix of transport)
  , transTerm
  , apTerm
  , lamTerm
  , Var <$> identifier
  , parens termP
  ]

lamTerm :: Parser Term
lamTerm = do
  _ <- symbol "\\" <|> symbol "λ"
  x <- identifier
  _ <- symbol ":"
  ty <- typeP
  _ <- symbol "."
  Lam x ty <$> termP

ifTerm :: Parser Term
ifTerm = do
  _ <- symbol "if"
  t1 <- termP
  _ <- symbol "then"
  t2 <- termP
  _ <- symbol "else"
  TmIf t1 t2 <$> termP

succTerm :: Parser Term
succTerm = TmSucc <$> (symbol "succ" *> termAtom)

predTerm :: Parser Term
predTerm = TmPred <$> (symbol "pred" *> termAtom)

isZeroTerm :: Parser Term
isZeroTerm = TmIsZero <$> (symbol "iszero" *> termAtom)

pairTerm :: Parser Term
pairTerm = do
  _ <- symbol "<"
  t1 <- termP
  _ <- symbol ","
  t2 <- termP
  _ <- symbol ">"
  return $ TmPair t1 t2

fstTerm :: Parser Term
fstTerm = TmFst <$> (symbol "fst" *> termAtom)

sndTerm :: Parser Term
sndTerm = TmSnd <$> (symbol "snd" *> termAtom)

inlTerm :: Parser Term
inlTerm = do
  _ <- symbol "inl"
  t <- termAtom
  _ <- symbol "as"
  TmInl t <$> typeP

inrTerm :: Parser Term
inrTerm = do
  _ <- symbol "inr"
  t <- termAtom
  _ <- symbol "as"
  TmInr t <$> typeP

caseTerm :: Parser Term
caseTerm = do
  _ <- symbol "case"
  t <- termP
  _ <- symbol "of"
  _ <- symbol "inl"
  x1 <- identifier
  _ <- symbol "=>"
  t1 <- termP
  _ <- symbol "|"
  _ <- symbol "inr"
  x2 <- identifier
  _ <- symbol "=>"
  TmCase t x1 t1 x2 <$> termP

letTerm :: Parser Term
letTerm = do
  _ <- symbol "let"
  x <- identifier
  _ <- symbol "="
  t1 <- termP
  _ <- symbol "in"
  TmLet x t1 <$> termP

absurdTerm :: Parser Term
absurdTerm = do
  _ <- symbol "absurd"
  ty <- brackets typeP
  TmAbsurd ty <$> termAtom

-- refl [A] a
reflTerm :: Parser Term
reflTerm = do
  _ <- symbol "refl"
  ty <- brackets typeP
  TmRefl ty <$> termAtom

-- J [C] base a b p
jTerm :: Parser Term
jTerm = do
  _ <- symbol "J"
  resultTy <- brackets typeP
  base <- termAtom
  a <- termAtom
  b <- termAtom
  p <- termAtom
  return $ TmJ resultTy base a b p

-- sym p
symTerm :: Parser Term
symTerm = TmSym <$> (symbol "sym" *> termAtom)

-- trans p q
transTerm :: Parser Term
transTerm = do
  _ <- symbol "trans"
  p <- termAtom
  TmTrans p <$> termAtom

-- ap f p
apTerm :: Parser Term
apTerm = do
  _ <- symbol "ap"
  f <- termAtom
  TmAp f <$> termAtom

-- transport [P] p t
transportTerm :: Parser Term
transportTerm = do
  _ <- symbol "transport"
  ty <- brackets typeP
  p <- termAtom
  TmTransport ty p <$> termAtom
