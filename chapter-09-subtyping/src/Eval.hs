{-# LANGUAGE LambdaCase #-}

module Eval
  ( -- * Evaluation
    eval
  , evalStep
    -- * Values
  , isValue
    -- * Normal forms
  , normalize
  ) where

import Syntax
import qualified Data.Map.Strict as Map

-- =============================================================================
-- Values
-- =============================================================================

-- | Check if a term is a value
--
-- Values in STLC with subtyping:
-- - Lambda abstractions
-- - Boolean literals
-- - Natural number values (zero, succ of value)
-- - Record values (all fields are values)
isValue :: Term -> Bool
isValue = \case
  Lam {} -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isValue t
  TmRecord fields -> all isValue (Map.elems fields)
  -- Ascription is not a value - it should evaluate away
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

-- | Small-step evaluation: one step of reduction
-- Returns Nothing if no reduction is possible
evalStep :: Term -> Maybe Term
evalStep = \case
  -- Variables don't reduce
  Var _ -> Nothing

  -- Lambda values don't reduce
  Lam {} -> Nothing

  -- Application
  App t1 t2 ->
    case t1 of
      -- β-reduction: (λx:τ. t) v → [x ↦ v]t
      Lam x _ body | isValue t2 ->
        Just $ substVar x t2 body
      -- Reduce function position first
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

  -- Records
  TmRecord fields ->
    -- Evaluate fields left-to-right
    case evalFirstField (Map.toList fields) of
      Just fields' -> Just $ TmRecord (Map.fromList fields')
      Nothing -> Nothing

  -- Projection
  TmProj t label ->
    case t of
      TmRecord fields | all isValue (Map.elems fields) ->
        Map.lookup label fields
      _ | not (isValue t) ->
        TmProj <$> evalStep t <*> pure label
      _ -> Nothing

  -- Ascription: strip it when the term is a value
  -- (t as T) → t  when t is a value
  TmAscribe t ty ->
    if isValue t
      then Just t
      else TmAscribe <$> evalStep t <*> pure ty

-- | Evaluate the first non-value field in a record
evalFirstField :: [(Label, Term)] -> Maybe [(Label, Term)]
evalFirstField [] = Nothing
evalFirstField ((l, t):rest)
  | isValue t =
    ((l, t) :) <$> evalFirstField rest
  | otherwise =
    case evalStep t of
      Just t' -> Just ((l, t') : rest)
      Nothing -> Nothing

-- =============================================================================
-- Multi-Step Evaluation
-- =============================================================================

-- | Fully evaluate a term to a value (or stuck term)
eval :: Term -> Term
eval t =
  case evalStep t of
    Just t' -> eval t'
    Nothing -> t

-- | Normalize a term (same as eval for this simple calculus)
normalize :: Term -> Term
normalize = eval
