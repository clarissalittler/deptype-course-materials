{-# LANGUAGE LambdaCase #-}

module Eval
  ( -- * Evaluation
    eval
  , evalStep
    -- * Values
  , isValue
  ) where

import Syntax
import qualified Data.Map as Map

-- =============================================================================
-- Values
-- =============================================================================

isValue :: Term -> Bool
isValue = \case
  Lam {} -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isNumericValue t
  TmUnit -> True
  TmRecord fields -> all isValue (Map.elems fields)
  TmVariant _ t _ -> isValue t
  TmRowAbs {} -> True
  _ -> False

isNumericValue :: Term -> Bool
isNumericValue = \case
  TmZero -> True
  TmSucc t -> isNumericValue t
  _ -> False

-- =============================================================================
-- Evaluation
-- =============================================================================

eval :: Term -> Term
eval t = case evalStep t of
  Nothing -> t
  Just t' -> eval t'

evalStep :: Term -> Maybe Term
evalStep = \case
  Var _ -> Nothing
  Lam {} -> Nothing

  App t1 t2
    | not (isValue t1) -> App <$> evalStep t1 <*> pure t2
    | not (isValue t2) -> App t1 <$> evalStep t2
    | Lam x _ body <- t1 -> Just $ substVar x t2 body
    | otherwise -> Nothing

  TmTrue -> Nothing
  TmFalse -> Nothing

  TmIf t1 t2 t3
    | not (isValue t1) -> (\t1' -> TmIf t1' t2 t3) <$> evalStep t1
    | TmTrue <- t1 -> Just t2
    | TmFalse <- t1 -> Just t3
    | otherwise -> Nothing

  TmZero -> Nothing

  TmSucc t
    | not (isValue t) -> TmSucc <$> evalStep t
    | otherwise -> Nothing

  TmPred t
    | not (isValue t) -> TmPred <$> evalStep t
    | TmZero <- t -> Just TmZero
    | TmSucc n <- t, isNumericValue n -> Just n
    | otherwise -> Nothing

  TmIsZero t
    | not (isValue t) -> TmIsZero <$> evalStep t
    | TmZero <- t -> Just TmTrue
    | TmSucc n <- t, isNumericValue n -> Just TmFalse
    | otherwise -> Nothing

  TmUnit -> Nothing

  TmRecord fields ->
    case stepFields fields of
      Just fields' -> Just $ TmRecord fields'
      Nothing -> Nothing

  TmProj t l
    | not (isValue t) -> TmProj <$> evalStep t <*> pure l
    | TmRecord fields <- t -> Map.lookup l fields
    | otherwise -> Nothing

  TmExtend t1 l t2
    | not (isValue t1) -> (\t1' -> TmExtend t1' l t2) <$> evalStep t1
    | not (isValue t2) -> TmExtend t1 l <$> evalStep t2
    | TmRecord fields <- t1 -> Just $ TmRecord (Map.insert l t2 fields)
    | otherwise -> Nothing

  TmRestrict t l
    | not (isValue t) -> TmRestrict <$> evalStep t <*> pure l
    | TmRecord fields <- t -> Just $ TmRecord (Map.delete l fields)
    | otherwise -> Nothing

  TmVariant l t ty
    | not (isValue t) -> (\t' -> TmVariant l t' ty) <$> evalStep t
    | otherwise -> Nothing

  TmCase t cases
    | not (isValue t) -> (\t' -> TmCase t' cases) <$> evalStep t
    | TmVariant l v _ <- t ->
        case lookup l [(lbl, (x, body)) | (lbl, x, body) <- cases] of
          Just (x, body) -> Just $ substVar x v body
          Nothing -> Nothing
    | otherwise -> Nothing

  TmLet x t1 t2
    | not (isValue t1) -> (\t1' -> TmLet x t1' t2) <$> evalStep t1
    | otherwise -> Just $ substVar x t1 t2

  TmRowAbs {} -> Nothing

  TmRowApp t row
    | not (isValue t) -> (\t' -> TmRowApp t' row) <$> evalStep t
    | TmRowAbs _ body <- t -> Just body
    | otherwise -> Nothing

-- | Step one field in a record
stepFields :: Map.Map Label Term -> Maybe (Map.Map Label Term)
stepFields fields = go (Map.toList fields)
  where
    go [] = Nothing
    go ((l, t):rest)
      | not (isValue t) = do
          t' <- evalStep t
          Just $ Map.fromList ((l, t') : rest)
      | otherwise = do
          rest' <- go rest
          Just $ Map.insert l t rest'
