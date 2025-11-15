{-# LANGUAGE LambdaCase #-}

module Eval
  ( Value, isValue
  , step, eval
  , normalizeType
  ) where

import Syntax

-- | Values (terms that cannot be reduced further)
type Value = Term

-- | Check if a term is a value
isValue :: Term -> Bool
isValue = \case
  Lam {} -> True
  TyAbs {} -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isNatValue t
  _ -> False

-- | Check if a term is a natural number value
isNatValue :: Term -> Bool
isNatValue = \case
  TmZero -> True
  TmSucc t -> isNatValue t
  _ -> False

-- | Type-level beta reduction: (λα::κ. τ) τ' → [α ↦ τ']τ
-- Normalize a type by performing type-level beta reductions
normalizeType :: Type -> Type
normalizeType = \case
  TyVar a -> TyVar a
  TyArr t1 t2 -> TyArr (normalizeType t1) (normalizeType t2)
  TyForall a k t -> TyForall a k (normalizeType t)
  TyLam a k t -> TyLam a k (normalizeType t)
  TyApp t1 t2 ->
    let t1' = normalizeType t1
        t2' = normalizeType t2
    in case t1' of
      TyLam a _ body -> normalizeType (substTyVarType a t2' body)
      _ -> TyApp t1' t2'
  TyBool -> TyBool
  TyNat -> TyNat

-- | Single-step call-by-value evaluation
step :: Term -> Maybe Term
step = \case
  -- E-App1: evaluate function first
  App t1 t2 | not (isValue t1) ->
    App <$> step t1 <*> pure t2

  -- E-App2: then evaluate argument
  App v1 t2 | isValue v1, not (isValue t2) ->
    App v1 <$> step t2

  -- E-AppAbs: beta reduction
  App (Lam x _ t) v2 | isValue v2 ->
    Just (substVar x v2 t)

  -- E-TApp: evaluate term before type application
  TyAppTerm t ty | not (isValue t) ->
    flip TyAppTerm ty <$> step t

  -- E-TAppTAbs: type application to type abstraction
  TyAppTerm (TyAbs a _ t) ty ->
    Just (substTyVar a ty t)

  -- E-IfTrue
  TmIf TmTrue t2 _ -> Just t2

  -- E-IfFalse
  TmIf TmFalse _ t3 -> Just t3

  -- E-If: evaluate guard first
  TmIf t1 t2 t3 | not (isValue t1) ->
    (\t1' -> TmIf t1' t2 t3) <$> step t1

  -- E-Succ: evaluate argument
  TmSucc t | not (isNatValue t) ->
    TmSucc <$> step t

  -- E-PredZero
  TmPred TmZero -> Just TmZero

  -- E-PredSucc
  TmPred (TmSucc nv) | isNatValue nv -> Just nv

  -- E-Pred: evaluate argument
  TmPred t | not (isNatValue t) ->
    TmPred <$> step t

  -- E-IsZeroZero
  TmIsZero TmZero -> Just TmTrue

  -- E-IsZeroSucc
  TmIsZero (TmSucc nv) | isNatValue nv -> Just TmFalse

  -- E-IsZero: evaluate argument
  TmIsZero t | not (isNatValue t) ->
    TmIsZero <$> step t

  -- No rule applies (value or stuck)
  _ -> Nothing

-- | Multi-step evaluation to normal form
eval :: Term -> Term
eval t = case step t of
  Just t' -> eval t'
  Nothing -> t
