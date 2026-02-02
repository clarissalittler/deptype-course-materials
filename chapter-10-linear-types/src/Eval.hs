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
  TmPair t1 t2 -> isValue t1 && isValue t2
  TmBang t -> isValue t
  _ -> False

-- | Check if a term is a numeric value
isNumericValue :: Term -> Bool
isNumericValue = \case
  TmZero -> True
  TmSucc t -> isNumericValue t
  _ -> False

-- =============================================================================
-- Small-Step Evaluation (Call-by-Value)
-- =============================================================================

-- | Small-step evaluation
evalStep :: Term -> Maybe Term
evalStep = \case
  -- Variables don't reduce
  Var _ -> Nothing

  -- Lambda values don't reduce
  Lam {} -> Nothing

  -- Application
  App t1 t2 ->
    case t1 of
      -- β-reduction
      Lam x _ _ body | isValue t2 ->
        Just $ substVar x t2 body
      -- Reduce function first
      _ | not (isValue t1) ->
        App <$> evalStep t1 <*> pure t2
      -- Then reduce argument
      _ | not (isValue t2) ->
        App t1 <$> evalStep t2
      _ -> Nothing

  -- Booleans
  TmTrue -> Nothing
  TmFalse -> Nothing

  -- Conditional
  TmIf t1 t2 t3 ->
    case t1 of
      TmTrue -> Just t2
      TmFalse -> Just t3
      _ -> TmIf <$> evalStep t1 <*> pure t2 <*> pure t3

  -- Natural numbers
  TmZero -> Nothing

  TmSucc t ->
    if isValue t
      then Nothing
      else TmSucc <$> evalStep t

  TmPred t ->
    case t of
      TmZero -> Just TmZero
      TmSucc nv | isNumericValue nv -> Just nv
      _ -> TmPred <$> evalStep t

  TmIsZero t ->
    case t of
      TmZero -> Just TmTrue
      TmSucc nv | isNumericValue nv -> Just TmFalse
      _ -> TmIsZero <$> evalStep t

  -- Unit
  TmUnit -> Nothing

  -- Pairs
  TmPair t1 t2
    | not (isValue t1) -> TmPair <$> evalStep t1 <*> pure t2
    | not (isValue t2) -> TmPair t1 <$> evalStep t2
    | otherwise -> Nothing

  -- Let-pair elimination
  TmLetPair x y t1 t2 ->
    case t1 of
      TmPair v1 v2 | isValue v1 && isValue v2 ->
        Just $ substVar x v1 (substVar y v2 t2)
      _ | not (isValue t1) ->
        TmLetPair x y <$> evalStep t1 <*> pure t2
      _ -> Nothing

  -- Bang
  TmBang t
    | isValue t -> Nothing
    | otherwise -> TmBang <$> evalStep t

  -- Let-bang elimination
  TmLetBang x t1 t2 ->
    case t1 of
      TmBang v | isValue v ->
        Just $ substVar x v t2
      _ | not (isValue t1) ->
        TmLetBang x <$> evalStep t1 <*> pure t2
      _ -> Nothing

  -- Let binding
  TmLet x m t1 t2
    | isValue t1 -> Just $ substVar x t1 t2
    | otherwise -> TmLet x m <$> evalStep t1 <*> pure t2

-- =============================================================================
-- Multi-Step Evaluation
-- =============================================================================

-- | Fully evaluate a term to a value
eval :: Term -> Term
eval t =
  case evalStep t of
    Just t' -> eval t'
    Nothing -> t
