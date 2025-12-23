{-# LANGUAGE LambdaCase #-}

module Eval
  ( eval
  , evalStep
  , isValue
  , evalMod
  ) where

import Syntax
import qualified Data.Map.Strict as Map

-- | Check if a term is a value
isValue :: Term -> Bool
isValue = \case
  Lam {} -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isValue t
  TmRecord fields -> all isValue (Map.elems fields)
  _ -> False

-- | Single-step evaluation
evalStep :: Term -> Maybe Term
evalStep = \case
  -- Beta reduction
  App (Lam x _ body) v
    | isValue v -> Just $ substVar x v body

  -- Application - evaluate function
  App t1 t2
    | not (isValue t1) -> App <$> evalStep t1 <*> pure t2

  -- Application - evaluate argument
  App v t
    | isValue v -> App v <$> evalStep t

  -- Conditional
  TmIf TmTrue t2 _ -> Just t2
  TmIf TmFalse _ t3 -> Just t3
  TmIf t1 t2 t3 -> (\t1' -> TmIf t1' t2 t3) <$> evalStep t1

  -- Successor
  TmSucc t
    | not (isValue t) -> TmSucc <$> evalStep t

  -- Predecessor
  TmPred TmZero -> Just TmZero
  TmPred (TmSucc n)
    | isValue n -> Just n
  TmPred t -> TmPred <$> evalStep t

  -- Zero test
  TmIsZero TmZero -> Just TmTrue
  TmIsZero (TmSucc _) -> Just TmFalse
  TmIsZero t -> TmIsZero <$> evalStep t

  -- Record projection
  TmProj (TmRecord fields) label
    | all isValue (Map.elems fields) ->
        Map.lookup label fields
  TmProj t label -> (`TmProj` label) <$> evalStep t

  -- Module projection - already a value (path-based access)
  TmModProj {} -> Nothing

  -- Values don't reduce
  _ -> Nothing

-- | Multi-step evaluation (normalize to a value)
eval :: Term -> Term
eval t = case evalStep t of
  Nothing -> t
  Just t' -> eval t'

-- | Evaluate a module expression
-- For now, modules evaluate to themselves (no module-level computation)
evalMod :: ModExpr -> ModExpr
evalMod = id  -- Modules are already values in our simple system
