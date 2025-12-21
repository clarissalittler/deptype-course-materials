{-# LANGUAGE LambdaCase #-}

module Eval
  ( -- * Evaluation
    eval
  , evalStep
    -- * Values
  , isValue
    -- * Computation results
  , Result(..)
  ) where

import Syntax

-- =============================================================================
-- Computation Results
-- =============================================================================

-- | Result of evaluating a computation
--
-- A computation either:
-- - Returns a value
-- - Performs an effect operation (suspended)
data Result
  = Done Term                           -- ^ Pure value
  | Suspended EffectLabel String Term (Term -> Term)
                                        -- ^ Suspended on effect op with continuation

instance Show Result where
  show (Done t) = "Done " ++ show t
  show (Suspended eff op arg _) =
    "Suspended " ++ eff ++ "." ++ op ++ " " ++ show arg ++ " <continuation>"

instance Eq Result where
  Done t1 == Done t2 = t1 == t2
  _ == _ = False

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
  TmEffAbs {} -> True
  TmReturn t -> isValue t
  _ -> False

-- | Check if a term is a numeric value
isNumericValue :: Term -> Bool
isNumericValue = \case
  TmZero -> True
  TmSucc t -> isNumericValue t
  _ -> False

-- =============================================================================
-- Evaluation
-- =============================================================================

-- | Evaluate a term to a value (or suspended computation)
eval :: Term -> Term
eval t = case evalStep t of
  Nothing -> t  -- Already a value or stuck
  Just t' -> eval t'

-- | Single step evaluation
evalStep :: Term -> Maybe Term
evalStep = \case
  -- Variables don't step
  Var _ -> Nothing

  -- Lambda values don't step
  Lam {} -> Nothing

  -- Application
  App t1 t2
    | not (isValue t1) -> App <$> evalStep t1 <*> pure t2
    | not (isValue t2) -> App t1 <$> evalStep t2
    | Lam x _ body <- t1 -> Just $ substVar x t2 body
    | otherwise -> Nothing

  -- Boolean values
  TmTrue -> Nothing
  TmFalse -> Nothing

  -- If-then-else
  TmIf t1 t2 t3
    | not (isValue t1) -> (\t1' -> TmIf t1' t2 t3) <$> evalStep t1
    | TmTrue <- t1 -> Just t2
    | TmFalse <- t1 -> Just t3
    | otherwise -> Nothing

  -- Numeric values
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

  -- Unit
  TmUnit -> Nothing

  -- Let binding
  TmLet x t1 t2
    | not (isValue t1) -> (\t1' -> TmLet x t1' t2) <$> evalStep t1
    | otherwise -> Just $ substVar x t1 t2

  -- Effect operations - these create suspended computations
  TmPerform eff op t
    | not (isValue t) -> (\t' -> TmPerform eff op t') <$> evalStep t
    | otherwise -> Nothing  -- Stuck: needs a handler

  -- Effect handlers
  TmHandle t h
    | not (isValue t) ->
        case evalStep t of
          Just t' -> Just $ TmHandle t' h
          Nothing ->
            -- Check if t is a perform that we can handle
            case t of
              TmPerform eff op arg
                | eff == handlerEffect h ->
                    -- Find the operation clause
                    case findOpClause op (handlerOps h) of
                      Just (_, paramVar, contVar, body) ->
                        -- Build the continuation
                        let cont = Lam "x" TyUnit (TmHandle (Var "x") h)
                            body' = substVar paramVar arg $
                                    substVar contVar cont body
                        in Just body'
                      Nothing -> Nothing  -- Op not handled
                | otherwise -> Nothing  -- Different effect
              _ -> Nothing
    | TmReturn v <- t, isValue v ->
        -- Apply return clause
        let (retVar, retBody) = handlerReturn h
        in Just $ substVar retVar v retBody
    | isValue t ->
        -- Value reaches handler, apply return clause
        let (retVar, retBody) = handlerReturn h
        in Just $ substVar retVar t retBody
    | otherwise -> Nothing

  -- Effect abstraction (value)
  TmEffAbs {} -> Nothing

  -- Effect application
  TmEffApp t _
    | not (isValue t) -> (\t' -> TmEffApp t' undefined) <$> evalStep t
    | TmEffAbs _ body <- t -> Just body  -- Erase effect abstraction
    | otherwise -> Nothing

  -- Return (value wrapper)
  TmReturn t
    | not (isValue t) -> TmReturn <$> evalStep t
    | otherwise -> Nothing

-- | Find an operation clause in a handler
findOpClause :: String -> [(String, Var, Var, Term)] -> Maybe (String, Var, Var, Term)
findOpClause _ [] = Nothing
findOpClause op (clause@(opName, _, _, _):rest)
  | op == opName = Just clause
  | otherwise = findOpClause op rest
