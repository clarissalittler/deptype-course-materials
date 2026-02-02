{-# LANGUAGE LambdaCase #-}

module Eval
  ( -- * Evaluation
    eval
  , evalStep
    -- * Values
  , isValue
  ) where

import Syntax

-- =============================================================================
-- Values
-- =============================================================================

-- | Check if a term is a value
isValue :: Term -> Bool
isValue = \case
  Lam {} -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isNumericValue t
  TmUnit -> True
  _ -> False

-- | Check if a term is a numeric value (0, succ 0, succ succ 0, ...)
isNumericValue :: Term -> Bool
isNumericValue = \case
  TmZero -> True
  TmSucc t -> isNumericValue t
  _ -> False

-- =============================================================================
-- Evaluation
-- =============================================================================

-- | Evaluate a term to a value
eval :: Term -> Term
eval t = case evalStep t of
  Nothing -> t  -- Already a value (or stuck)
  Just t' -> eval t'

-- | Single step evaluation
evalStep :: Term -> Maybe Term
evalStep = \case
  -- Variables don't step (stuck or values in a context)
  Var _ -> Nothing

  -- Lambda values don't step
  Lam {} -> Nothing

  -- Application
  App t1 t2
    | not (isValue t1) -> App <$> evalStep t1 <*> pure t2
    | not (isValue t2) -> App t1 <$> evalStep t2
    | Lam x _ body <- t1 -> Just $ substVar x t2 body
    | otherwise -> Nothing

  -- Boolean values don't step
  TmTrue -> Nothing
  TmFalse -> Nothing

  -- If-then-else
  TmIf t1 t2 t3
    | not (isValue t1) -> (\t1' -> TmIf t1' t2 t3) <$> evalStep t1
    | TmTrue <- t1 -> Just t2
    | TmFalse <- t1 -> Just t3
    | otherwise -> Nothing

  -- Numeric values don't step
  TmZero -> Nothing

  -- Successor
  TmSucc t
    | not (isValue t) -> TmSucc <$> evalStep t
    | otherwise -> Nothing

  -- Predecessor
  TmPred t
    | not (isValue t) -> TmPred <$> evalStep t
    | TmZero <- t -> Just TmZero
    | TmSucc n <- t, isNumericValue n -> Just n
    | otherwise -> Nothing

  -- IsZero
  TmIsZero t
    | not (isValue t) -> TmIsZero <$> evalStep t
    | TmZero <- t -> Just TmTrue
    | TmSucc n <- t, isNumericValue n -> Just TmFalse
    | otherwise -> Nothing

  -- Arithmetic
  TmArith op t1 t2
    | not (isValue t1) -> (\t1' -> TmArith op t1' t2) <$> evalStep t1
    | not (isValue t2) -> TmArith op t1 <$> evalStep t2
    | otherwise -> evalArith op t1 t2

  -- Unit value doesn't step
  TmUnit -> Nothing

  -- Let binding
  TmLet x t1 t2
    | not (isValue t1) -> (\t1' -> TmLet x t1' t2) <$> evalStep t1
    | otherwise -> Just $ substVar x t1 t2

  -- Ascription (just strip it if value)
  TmAscribe t ty
    | isValue t -> Just t
    | otherwise -> (\t' -> TmAscribe t' ty) <$> evalStep t

-- | Evaluate arithmetic operations
evalArith :: ArithOp -> Term -> Term -> Maybe Term
evalArith op t1 t2 = do
  n1 <- termToNat t1
  n2 <- termToNat t2
  let result = case op of
        Add -> n1 + n2
        Sub -> max 0 (n1 - n2)  -- Natural subtraction
  Just $ natToTerm result

-- | Convert a numeric value to a natural number
termToNat :: Term -> Maybe Int
termToNat = \case
  TmZero -> Just 0
  TmSucc t -> (+ 1) <$> termToNat t
  _ -> Nothing

-- | Convert a natural number to a term
natToTerm :: Int -> Term
natToTerm n
  | n <= 0 = TmZero
  | otherwise = TmSucc (natToTerm (n - 1))
