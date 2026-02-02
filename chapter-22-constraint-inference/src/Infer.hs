{-# LANGUAGE LambdaCase #-}

module Infer
  ( -- * Type inference
    infer
  , inferType
  , InferenceError(..)
  , showInferenceError
    -- * Re-exports
  , module Constraint
  , module Solve
  ) where

import Syntax
import Constraint
import Solve

-- | Inference errors (combining constraint and solve errors)
data InferenceError
  = ConstraintErr ConstraintError
  | SolveErr SolveError
  deriving (Eq, Show)

-- | Two-phase type inference
-- Phase 1: Generate constraints
-- Phase 2: Solve constraints
inferType :: Term -> Either InferenceError (ConstraintSet, Subst, Type)
inferType t = do
  -- Phase 1: Generate constraints
  (constraints, ty) <- case generateConstraints t of
    Left err -> Left (ConstraintErr err)
    Right res -> Right res

  -- Phase 2: Solve constraints
  subst <- case solve constraints of
    Left err -> Left (SolveErr err)
    Right s -> Right s

  -- Apply substitution to the inferred type
  let finalType = applySubst subst ty

  return (constraints, subst, finalType)

-- | Simple inference function that returns just the type
infer :: Term -> Either InferenceError Type
infer t = do
  (_, _, ty) <- inferType t
  return ty

-- | Pretty-print inference error
showInferenceError :: InferenceError -> String
showInferenceError = \case
  ConstraintErr (UnboundVariable x) ->
    "Unbound variable: " ++ x
  SolveErr (UnificationFail t1 t2) ->
    "Cannot unify " ++ show t1 ++ " with " ++ show t2
  SolveErr (OccursCheck a t) ->
    "Occurs check: " ++ a ++ " occurs in " ++ show t
  SolveErr (InfiniteType a t) ->
    "Infinite type: " ++ a ++ " = " ++ show t
