{-# LANGUAGE LambdaCase #-}

module Eval
  ( -- * Evaluation strategies
    eval
  , evalNormal
  , evalCallByName
  , evalCallByValue
    -- * Single-step reduction
  , step
  , stepNormal
  , stepCallByName
  , stepCallByValue
    -- * Normalization
  , normalize
  , normalizeWith
  , normalizeSteps
  , normalizeStepsWith
  , isValue
  , isNormalForm
  ) where

import Syntax

-- | Check if a term is a value (for call-by-value semantics)
-- In untyped lambda calculus, only lambda abstractions are values
isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue _ = False

-- | Check if a term is in normal form (cannot be reduced further)
isNormalForm :: Term -> Bool
isNormalForm = \case
  Var _ -> True
  Lam _ t -> isNormalForm t
  App (Lam _ _) _ -> False  -- This is a redex
  App t1 t2 -> isNormalForm t1 && isNormalForm t2

-- | Call-by-value single-step evaluation
-- Reduces the leftmost-innermost redex (does not reduce under lambdas)
stepCallByValue :: Term -> Maybe Term
stepCallByValue = \case
  Var _ -> Nothing
  Lam _ _ -> Nothing
  App t1 t2
    | not (isValue t1) ->
        (\t1' -> App t1' t2) <$> stepCallByValue t1
    | Lam x t <- t1, isValue t2 ->
        Just (substVar x t2 t)  -- β-reduction
    | Lam _ _ <- t1 ->
        App t1 <$> stepCallByValue t2  -- Evaluate argument after function
    | otherwise -> Nothing

-- | Call-by-name single-step evaluation
-- Reduces the leftmost-outermost redex without reducing under lambdas
stepCallByName :: Term -> Maybe Term
stepCallByName = \case
  Var _ -> Nothing
  Lam _ _ -> Nothing
  App (Lam x t) t2 -> Just (substVar x t2 t)  -- β-reduction
  App t1 t2 -> App <$> stepCallByName t1 <*> pure t2

-- | Normal order reduction (leftmost-outermost redex)
-- This is guaranteed to find a normal form if one exists
stepNormal :: Term -> Maybe Term
stepNormal = \case
  Var _ -> Nothing
  Lam x t -> Lam x <$> stepNormal t
  App (Lam x t) t2 -> Just (substVar x t2 t)  -- β-reduction
  App t1 t2 ->
    case stepNormal t1 of
      Just t1' -> Just (App t1' t2)
      Nothing -> App t1 <$> stepNormal t2

-- | Generic single-step reduction (normal order by default)
step :: Term -> Maybe Term
step = stepNormal

-- | Evaluate to normal form using the given step function
-- Returns Nothing if evaluation doesn't terminate within maxSteps
normalizeWith :: Int -> (Term -> Maybe Term) -> Term -> Maybe Term
normalizeWith maxSteps stepFn = go maxSteps
  where
    go 0 _ = Nothing  -- Hit step limit
    go n t = case stepFn t of
      Nothing -> Just t  -- Already in normal form
      Just t' -> go (n - 1) t'

-- | Normalize a term (up to 1000 steps)
normalize :: Term -> Maybe Term
normalize = normalizeWith 1000 stepNormal

-- | Normalize and return all intermediate steps
normalizeSteps :: Term -> [Term]
normalizeSteps = normalizeStepsWith 1000 stepNormal

-- | Normalize with a specific step function and collect steps
normalizeStepsWith :: Int -> (Term -> Maybe Term) -> Term -> [Term]
normalizeStepsWith maxSteps stepFn = go maxSteps
  where
    go 0 t = [t]
    go n t = case stepFn t of
      Nothing -> [t]
      Just t' -> t : go (n - 1) t'

-- | Evaluate using normal order reduction
evalNormal :: Term -> Term
evalNormal t = case normalize t of
  Just t' -> t'
  Nothing -> t  -- Return original if doesn't normalize

-- | Evaluate using call-by-name
evalCallByName :: Term -> Term
evalCallByName t = case normalizeWith 1000 stepCallByName t of
  Just t' -> t'
  Nothing -> t

-- | Evaluate using call-by-value
evalCallByValue :: Term -> Term
evalCallByValue t = case normalizeWith 1000 stepCallByValue t of
  Just t' -> t'
  Nothing -> t

-- | Default evaluation strategy (normal order)
eval :: Term -> Term
eval = evalNormal
