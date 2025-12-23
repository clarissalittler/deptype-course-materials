{-# LANGUAGE LambdaCase #-}

module Eval
  ( -- * Evaluation
    eval
  , eval1
  , isValue
    -- * Normal forms
  , normalize
  , nf
  ) where

import Syntax

-- | Check if a term is a value
isValue :: Term -> Bool
isValue = \case
  Lam {} -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isValue t
  TmPair t1 t2 -> isValue t1 && isValue t2
  TmNil -> True
  TmCons t1 t2 -> isValue t1 && isValue t2
  _ -> False

-- | One-step evaluation (call-by-value)
eval1 :: Term -> Maybe Term
eval1 = \case
  -- Application
  App (Lam x body) v | isValue v -> Just (substVar x v body)
  App v1 t2 | isValue v1 -> App v1 <$> eval1 t2
  App t1 t2 -> (`App` t2) <$> eval1 t1

  -- Let
  Let x v t | isValue v -> Just (substVar x v t)
  Let x t1 t2 -> (\t1' -> Let x t1' t2) <$> eval1 t1

  -- If
  TmIf TmTrue t2 _ -> Just t2
  TmIf TmFalse _ t3 -> Just t3
  TmIf t1 t2 t3 -> (\t1' -> TmIf t1' t2 t3) <$> eval1 t1

  -- Successor
  TmSucc t | not (isValue t) -> TmSucc <$> eval1 t

  -- Predecessor
  TmPred TmZero -> Just TmZero
  TmPred (TmSucc nv) | isValue nv -> Just nv
  TmPred t -> TmPred <$> eval1 t

  -- IsZero
  TmIsZero TmZero -> Just TmTrue
  TmIsZero (TmSucc nv) | isValue nv -> Just TmFalse
  TmIsZero t -> TmIsZero <$> eval1 t

  -- Pairs
  TmPair t1 t2
    | not (isValue t1) -> (\t1' -> TmPair t1' t2) <$> eval1 t1
    | not (isValue t2) -> TmPair t1 <$> eval1 t2

  TmFst (TmPair v1 v2) | isValue v1 && isValue v2 -> Just v1
  TmFst t -> TmFst <$> eval1 t

  TmSnd (TmPair v1 v2) | isValue v1 && isValue v2 -> Just v2
  TmSnd t -> TmSnd <$> eval1 t

  -- Lists
  TmCons t1 t2
    | not (isValue t1) -> (\t1' -> TmCons t1' t2) <$> eval1 t1
    | not (isValue t2) -> TmCons t1 <$> eval1 t2

  TmIsNil TmNil -> Just TmTrue
  TmIsNil (TmCons v1 v2) | isValue v1 && isValue v2 -> Just TmFalse
  TmIsNil t -> TmIsNil <$> eval1 t

  TmHead (TmCons v1 v2) | isValue v1 && isValue v2 -> Just v1
  TmHead t -> TmHead <$> eval1 t

  TmTail (TmCons v1 v2) | isValue v1 && isValue v2 -> Just v2
  TmTail t -> TmTail <$> eval1 t

  -- No reduction possible
  _ -> Nothing

-- | Multi-step evaluation
eval :: Term -> Term
eval t = case eval1 t of
  Nothing -> t
  Just t' -> eval t'

-- | Normalize to normal form
normalize :: Term -> Term
normalize = eval

-- | Alias for normalize
nf :: Term -> Term
nf = normalize
