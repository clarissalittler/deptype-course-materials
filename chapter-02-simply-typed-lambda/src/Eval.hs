{-# LANGUAGE LambdaCase #-}

module Eval
  ( -- * Values
    isValue
  , isNumericValue
    -- * Evaluation
  , step
  , eval
  , evalSteps
  , normalize
  ) where

import Syntax

-- | Check if a term is a value
isValue :: Term -> Bool
isValue = \case
  Lam _ _ _ -> True
  TmTrue -> True
  TmFalse -> True
  t | isNumericValue t -> True
  _ -> False

-- | Check if a term is a numeric value (0, succ 0, succ succ 0, ...)
isNumericValue :: Term -> Bool
isNumericValue = \case
  TmZero -> True
  TmSucc t -> isNumericValue t
  _ -> False

-- | Single-step call-by-value evaluation
step :: Term -> Maybe Term
step = \case
  -- Variables don't reduce
  Var _ -> Nothing

  -- Lambdas are values
  Lam _ _ _ -> Nothing

  -- E-AppAbs: (λx:T. t) v → [x ↦ v]t (when v is a value)
  App (Lam x _ t) v | isValue v ->
    Just (substVar x v t)

  -- E-App1: if t1 → t1', then t1 t2 → t1' t2
  App t1 t2 ->
    case step t1 of
      Just t1' -> Just (App t1' t2)
      Nothing ->
        -- E-App2: if t2 → t2', then v1 t2 → v1 t2' (when v1 is a value)
        if isValue t1
          then App t1 <$> step t2
          else Nothing

  -- Booleans are values
  TmTrue -> Nothing
  TmFalse -> Nothing

  -- E-IfTrue: if true then t2 else t3 → t2
  TmIf TmTrue t2 _ -> Just t2

  -- E-IfFalse: if false then t2 else t3 → t3
  TmIf TmFalse _ t3 -> Just t3

  -- E-If: if t1 → t1', then (if t1 then t2 else t3) → (if t1' then t2 else t3)
  TmIf t1 t2 t3 ->
    (\t1' -> TmIf t1' t2 t3) <$> step t1

  -- Zero is a value
  TmZero -> Nothing

  -- E-Succ: if t → t', then succ t → succ t'
  TmSucc t ->
    TmSucc <$> step t

  -- E-PredZero: pred 0 → 0
  TmPred TmZero -> Just TmZero

  -- E-PredSucc: pred (succ nv) → nv (when nv is a numeric value)
  TmPred (TmSucc t) | isNumericValue t -> Just t

  -- E-Pred: if t → t', then pred t → pred t'
  TmPred t ->
    TmPred <$> step t

  -- E-IsZeroZero: iszero 0 → true
  TmIsZero TmZero -> Just TmTrue

  -- E-IsZeroSucc: iszero (succ nv) → false (when nv is a numeric value)
  TmIsZero (TmSucc t) | isNumericValue t -> Just TmFalse

  -- E-IsZero: if t → t', then iszero t → iszero t'
  TmIsZero t ->
    TmIsZero <$> step t

-- | Evaluate to normal form (up to 1000 steps)
normalize :: Term -> Term
normalize = go (1000 :: Int)
  where
    go :: Int -> Term -> Term
    go 0 t = t  -- Give up after max steps
    go n t = case step t of
      Nothing -> t
      Just t' -> go (n - 1) t'

-- | Evaluate a term (same as normalize)
eval :: Term -> Term
eval = normalize

-- | Evaluate and return all intermediate steps
evalSteps :: Term -> [Term]
evalSteps = go (1000 :: Int)
  where
    go :: Int -> Term -> [Term]
    go 0 t = [t]
    go n t = case step t of
      Nothing -> [t]
      Just t' -> t : go (n - 1) t'
