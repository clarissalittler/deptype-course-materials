{-# LANGUAGE LambdaCase #-}

module Eval (eval, isValue, step) where

import Syntax

isValue :: Term -> Bool
isValue = \case
  Lam _ _ _ -> True
  TyAbs _ _ -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isValue t
  _ -> False

step :: Term -> Maybe Term
step = \case
  -- E-AppAbs: (λx:τ. t) v → [x ↦ v]t
  App (Lam x _ body) v | isValue v -> Just (substVar x v body)
  -- E-App1
  App t1 t2 | not (isValue t1) -> App <$> step t1 <*> pure t2
  -- E-App2
  App v1 t2 | isValue v1 -> App v1 <$> step t2

  -- E-TyAppTyAbs: (Λα. t) [τ] → [α ↦ τ]t
  TyApp (TyAbs a body) ty -> Just (substTyVar a ty body)
  -- E-TyApp
  TyApp t ty -> (`TyApp` ty) <$> step t

  -- Booleans
  TmIf TmTrue t2 _ -> Just t2
  TmIf TmFalse _ t3 -> Just t3
  TmIf t1 t2 t3 -> (\t1' -> TmIf t1' t2 t3) <$> step t1

  -- Natural numbers
  TmSucc t -> TmSucc <$> step t
  TmPred TmZero -> Just TmZero
  TmPred (TmSucc v) | isValue v -> Just v
  TmPred t -> TmPred <$> step t
  TmIsZero TmZero -> Just TmTrue
  TmIsZero (TmSucc v) | isValue v -> Just TmFalse
  TmIsZero t -> TmIsZero <$> step t

  _ -> Nothing

eval :: Term -> Term
eval t = case step t of
  Nothing -> t
  Just t' -> eval t'
