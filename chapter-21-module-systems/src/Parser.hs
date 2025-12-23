{-# LANGUAGE OverloadedStrings #-}

module Parser
  ( parseTerm
  , parseType
  , parseMod
  , parseSig
  ) where

import Syntax
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Map.Strict as Map
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr

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

-- | Parse an identifier
identifier :: Parser String
identifier = lexeme $ do
  first <- letterChar <|> char '_'
  rest <- many (alphaNumChar <|> char '_' <|> char '\'')
  let name = first : rest
  if name `elem` keywords
    then fail $ "keyword " ++ show name ++ " cannot be an identifier"
    else return name

-- | Reserved keywords
keywords :: [String]
keywords =
  [ "true", "false", "if", "then", "else"
  , "succ", "pred", "iszero"
  , "Bool", "Nat"
  , "struct", "end", "sig"
  , "val", "type", "module"
  , "functor"
  , "as"
  ]

-- | Parse parentheses
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Parse braces
braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

-- | Parse a type
parseType :: Text -> Either String Type
parseType input = case runParser (sc *> pType <* eof) "" input of
  Left err -> Left $ errorBundlePretty err
  Right ty -> Right ty

pType :: Parser Type
pType = makeExprParser pTypeAtom typeOperators

typeOperators :: [[Operator Parser Type]]
typeOperators =
  [ [InfixR (TyArr <$ symbol "->")]
  ]

pTypeAtom :: Parser Type
pTypeAtom = choice
  [ TyBool <$ symbol "Bool"
  , TyNat <$ symbol "Nat"
  , TyNamed <$> identifier
  , pRecordType
  , parens pType
  ]

pRecordType :: Parser Type
pRecordType = braces $ do
  fields <- pTypeField `sepBy` symbol ","
  return $ TyRecord (Map.fromList fields)

pTypeField :: Parser (Label, Type)
pTypeField = do
  label <- identifier
  _ <- symbol ":"
  ty <- pType
  return (label, ty)

-- | Parse a term
parseTerm :: Text -> Either String Term
parseTerm input = case runParser (sc *> pTerm <* eof) "" input of
  Left err -> Left $ errorBundlePretty err
  Right t -> Right t

pTerm :: Parser Term
pTerm = makeExprParser pTermAtom termOperators

termOperators :: [[Operator Parser Term]]
termOperators =
  [ [Postfix (pProjection <|> pApplication)]
  ]

pProjection :: Parser (Term -> Term)
pProjection = do
  _ <- symbol "."
  label <- identifier
  return (`TmProj` label)

pApplication :: Parser (Term -> Term)
pApplication = do
  args <- some pTermAtom
  return $ \f -> foldl App f args

pTermAtom :: Parser Term
pTermAtom = choice
  [ TmTrue <$ symbol "true"
  , TmFalse <$ symbol "false"
  , pNat
  , pIf
  , pSucc
  , pPred
  , pIsZero
  , pLambda
  , pRecord
  , pModProj
  , Var <$> identifier
  , parens pTerm
  ]

pNat :: Parser Term
pNat = lexeme L.decimal >>= natToTerm
  where
    natToTerm :: Integer -> Parser Term
    natToTerm 0 = return TmZero
    natToTerm n
      | n > 0 = return $ iterate TmSucc TmZero !! fromInteger n
      | otherwise = fail "Negative numbers not supported"

pIf :: Parser Term
pIf = do
  _ <- symbol "if"
  t1 <- pTerm
  _ <- symbol "then"
  t2 <- pTerm
  _ <- symbol "else"
  t3 <- pTerm
  return $ TmIf t1 t2 t3

pSucc :: Parser Term
pSucc = TmSucc <$> (symbol "succ" *> pTermAtom)

pPred :: Parser Term
pPred = TmPred <$> (symbol "pred" *> pTermAtom)

pIsZero :: Parser Term
pIsZero = TmIsZero <$> (symbol "iszero" *> pTermAtom)

pLambda :: Parser Term
pLambda = do
  _ <- symbol "\\" <|> symbol "λ"
  x <- identifier
  _ <- symbol ":"
  ty <- pType
  _ <- symbol "."
  body <- pTerm
  return $ Lam x ty body

pRecord :: Parser Term
pRecord = braces $ do
  fields <- pRecordField `sepBy` symbol ","
  return $ TmRecord (Map.fromList fields)

pRecordField :: Parser (Label, Term)
pRecordField = do
  label <- identifier
  _ <- symbol "="
  term <- pTerm
  return (label, term)

pModProj :: Parser Term
pModProj = try $ do
  path <- identifier `sepBy1` symbol "."
  case path of
    [_] -> fail "Not a module projection"
    _ -> do
      let mods = init path
          var = last path
      return $ TmModProj (ModPath mods var) var

-- | Parse a module expression
parseMod :: Text -> Either String ModExpr
parseMod input = case runParser (sc *> pModExpr <* eof) "" input of
  Left err -> Left $ errorBundlePretty err
  Right m -> Right m

pModExpr :: Parser ModExpr
pModExpr = choice
  [ pStruct
  , pFunctor
  , pSeal
  , pModApp
  , ModVar <$> identifier
  ]

pStruct :: Parser ModExpr
pStruct = do
  _ <- symbol "struct"
  decls <- many pDecl
  _ <- symbol "end"
  return $ Struct decls

pDecl :: Parser Decl
pDecl = choice
  [ pValDecl
  , pTypeDecl
  , pModDecl
  ]

pValDecl :: Parser Decl
pValDecl = do
  _ <- symbol "val"
  x <- identifier
  _ <- symbol ":"
  ty <- pType
  _ <- symbol "="
  t <- pTerm
  return $ ValDecl x ty t

pTypeDecl :: Parser Decl
pTypeDecl = do
  _ <- symbol "type"
  t <- identifier
  mty <- optional $ do
    _ <- symbol "="
    pType
  return $ TypeDecl t mty

pModDecl :: Parser Decl
pModDecl = do
  _ <- symbol "module"
  m <- identifier
  _ <- symbol "="
  mexpr <- pModExpr
  return $ ModDecl m mexpr

pFunctor :: Parser ModExpr
pFunctor = do
  _ <- symbol "functor"
  _ <- symbol "("
  x <- identifier
  _ <- symbol ":"
  sig <- pSigExpr
  _ <- symbol ")"
  _ <- symbol "=>"
  body <- pModExpr
  return $ Functor x sig body

pModApp :: Parser ModExpr
pModApp = try $ parens $ do
  mf <- pModExpr
  _ <- symbol "("
  marg <- pModExpr
  _ <- symbol ")"
  return $ ModApp mf marg

pSeal :: Parser ModExpr
pSeal = try $ parens $ do
  m <- pModExpr
  _ <- symbol ":>"
  sig <- pSigExpr
  return $ Seal m sig

-- | Parse a signature
parseSig :: Text -> Either String Signature
parseSig input = case runParser (sc *> pSigExpr <* eof) "" input of
  Left err -> Left $ errorBundlePretty err
  Right sig -> Right sig

pSigExpr :: Parser Signature
pSigExpr = do
  _ <- symbol "sig"
  specs <- many pSpec
  _ <- symbol "end"
  return $ Sig specs

pSpec :: Parser Spec
pSpec = choice
  [ pValSpec
  , pTypeSpec
  , pModSpec
  ]

pValSpec :: Parser Spec
pValSpec = do
  _ <- symbol "val"
  x <- identifier
  _ <- symbol ":"
  ty <- pType
  return $ ValSpec x ty

pTypeSpec :: Parser Spec
pTypeSpec = do
  _ <- symbol "type"
  t <- identifier
  mty <- optional $ do
    _ <- symbol "="
    pType
  return $ TypeSpec t mty

pModSpec :: Parser Spec
pModSpec = do
  _ <- symbol "module"
  m <- identifier
  _ <- symbol ":"
  sig <- pSigExpr
  return $ ModSpec m sig
