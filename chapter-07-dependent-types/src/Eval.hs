{-# LANGUAGE LambdaCase #-}

module Eval
  ( Value
  , eval
  , normalize
  , isValue
  , quote
  ) where

import Syntax

-- | Values (normal forms)
-- In dependent type theory, we often use a separate Value type
-- for efficiency, but here we'll use Term for simplicity
type Value = Term

-- | Check if a term is a value
isValue :: Term -> Bool
isValue = \case
  Type -> True
  Lam {} -> True
  Pi {} -> True
  Sigma {} -> True
  Pair v1 v2 -> isValue v1 && isValue v2
  Nat -> True
  Zero -> True
  Succ v -> isValue v
  Bool -> True
  TmTrue -> True
  TmFalse -> True
  _ -> False

-- | Single-step evaluation
step :: Term -> Maybe Term
step = \case
  -- Beta reduction for lambda
  App (Lam x _ t) v | isValue v -> Just (subst x v t)

  -- Reduce function in application
  App t1 t2 | not (isValue t1) ->
    App <$> step t1 <*> pure t2

  -- Reduce argument in application
  App v1 t2 | isValue v1, not (isValue t2) ->
    App v1 <$> step t2

  -- Pair projections
  Fst (Pair v1 v2) | isValue v1 && isValue v2 -> Just v1
  Fst t | not (isValue t) -> Fst <$> step t

  Snd (Pair v1 v2) | isValue v1 && isValue v2 -> Just v2
  Snd t | not (isValue t) -> Snd <$> step t

  -- Reduce inside pairs
  Pair t1 t2 | not (isValue t1) ->
    Pair <$> step t1 <*> pure t2
  Pair v1 t2 | isValue v1, not (isValue t2) ->
    Pair v1 <$> step t2

  -- Successor
  Succ t | not (isValue t) -> Succ <$> step t

  -- Boolean conditionals
  If TmTrue t2 _ -> Just t2
  If TmFalse _ t3 -> Just t3
  If t1 t2 t3 | not (isValue t1) ->
    (\t1' -> If t1' t2 t3) <$> step t1

  -- Reduce inside dependent types
  Pi x a b | not (isValue a) ->
    Pi x <$> step a <*> pure b

  Sigma x a b | not (isValue a) ->
    Sigma x <$> step a <*> pure b

  -- No reduction possible
  _ -> Nothing

-- | Evaluate to normal form
eval :: Term -> Term
eval t = case step t of
  Just t' -> eval t'
  Nothing -> t

-- | Normalize a term (same as eval for this implementation)
normalize :: Term -> Term
normalize = eval

-- | Quote a value back to a term (identity in our case)
quote :: Value -> Term
quote = id
