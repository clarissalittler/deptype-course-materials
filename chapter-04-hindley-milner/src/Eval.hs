{-# LANGUAGE LambdaCase #-}

module Eval (eval, isValue, step) where

import Syntax

isValue :: Term -> Bool
isValue = \case
  Lam _ _ -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isValue t
  TmPair v1 v2 -> isValue v1 && isValue v2
  TmNil -> True
  TmCons v1 v2 -> isValue v1 && isValue v2
  _ -> False

step :: Term -> Maybe Term
step = \case
  App (Lam x body) v | isValue v -> Just (substVar x v body)
  App t1 t2
    | not (isValue t1) -> App <$> step t1 <*> pure t2
    | not (isValue t2) -> App t1 <$> step t2
    | otherwise -> Nothing
  Let x v body | isValue v -> Just (substVar x v body)
  Let x t body -> (\t' -> Let x t' body) <$> step t
  TmIf TmTrue t2 _ -> Just t2
  TmIf TmFalse _ t3 -> Just t3
  TmIf t1 t2 t3 -> (\t1' -> TmIf t1' t2 t3) <$> step t1
  TmSucc t -> TmSucc <$> step t
  TmPred TmZero -> Just TmZero
  TmPred (TmSucc v) | isValue v -> Just v
  TmPred t -> TmPred <$> step t
  TmIsZero TmZero -> Just TmTrue
  TmIsZero (TmSucc v) | isValue v -> Just TmFalse
  TmIsZero t -> TmIsZero <$> step t
  TmPair t1 t2
    | not (isValue t1) -> TmPair <$> step t1 <*> pure t2
    | not (isValue t2) -> TmPair t1 <$> step t2
    | otherwise -> Nothing
  TmFst (TmPair v1 v2) | isValue v1 && isValue v2 -> Just v1
  TmFst t -> TmFst <$> step t
  TmSnd (TmPair v1 v2) | isValue v1 && isValue v2 -> Just v2
  TmSnd t -> TmSnd <$> step t
  TmCons t1 t2
    | not (isValue t1) -> TmCons <$> step t1 <*> pure t2
    | not (isValue t2) -> TmCons t1 <$> step t2
    | otherwise -> Nothing
  TmIsNil TmNil -> Just TmTrue
  TmIsNil (TmCons v1 v2) | isValue v1 && isValue v2 -> Just TmFalse
  TmIsNil t -> TmIsNil <$> step t
  TmHead (TmCons v1 v2) | isValue v1 && isValue v2 -> Just v1
  TmHead t -> TmHead <$> step t
  TmTail (TmCons v1 v2) | isValue v1 && isValue v2 -> Just v2
  TmTail t -> TmTail <$> step t
  _ -> Nothing

eval :: Term -> Term
eval t = case step t of
  Nothing -> t
  Just t' -> eval t'
