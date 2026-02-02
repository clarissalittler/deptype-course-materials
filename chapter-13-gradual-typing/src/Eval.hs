{-# LANGUAGE LambdaCase #-}

module Eval
  ( -- * Evaluation
    eval
  , evalStep
    -- * Values
  , isValue
    -- * Cast behavior
  , applyCast
  ) where

import Syntax

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
  -- A cast around a value is a value (for ground types)
  TmCast v ty1 ty2 _
    | isValue v && isGround ty1 && isGround ty2 -> True
    | isValue v && ty1 == TyDyn -> True
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

-- | Evaluate a term to a value (or blame)
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
    -- Cast applied to argument
    | TmCast v (TyFun t11 t12) (TyFun t21 t22) l <- t1, isValue v ->
        -- (v : T11->T12 => T21->T22) t2
        -- = (v (<T21 => T11> t2)) : T12 => T22
        let t2' = TmCast t2 t21 t11 l
            result = App v t2'
        in Just $ TmCast result t12 t22 l
    | otherwise -> Nothing

  -- Boolean values
  TmTrue -> Nothing
  TmFalse -> Nothing

  -- If-then-else
  TmIf t1 t2 t3
    | not (isValue t1) -> (\t1' -> TmIf t1' t2 t3) <$> evalStep t1
    | TmTrue <- t1 -> Just t2
    | TmFalse <- t1 -> Just t3
    -- Cast to Bool
    | TmCast v _ TyBool l <- t1, isValue v ->
        case v of
          TmTrue -> Just t2
          TmFalse -> Just t3
          _ -> Just $ TmBlame TyBool l  -- Not a boolean, blame!
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
    | TmCast v _ TyNat l <- t, isValue v ->
        case v of
          TmZero -> Just TmZero
          TmSucc n | isNumericValue n -> Just n
          _ -> Just $ TmBlame TyNat l
    | otherwise -> Nothing

  TmIsZero t
    | not (isValue t) -> TmIsZero <$> evalStep t
    | TmZero <- t -> Just TmTrue
    | TmSucc n <- t, isNumericValue n -> Just TmFalse
    | TmCast v _ TyNat l <- t, isValue v ->
        case v of
          TmZero -> Just TmTrue
          TmSucc n | isNumericValue n -> Just TmFalse
          _ -> Just $ TmBlame TyBool l
    | otherwise -> Nothing

  -- Unit
  TmUnit -> Nothing

  -- Let binding
  TmLet x t1 t2
    | not (isValue t1) -> (\t1' -> TmLet x t1' t2) <$> evalStep t1
    | otherwise -> Just $ substVar x t1 t2

  -- Casts
  TmCast t ty1 ty2 l
    | not (isValue t) -> (\t' -> TmCast t' ty1 ty2 l) <$> evalStep t
    | otherwise -> applyCast t ty1 ty2 l

  -- Ascription (remove if value)
  TmAscribe t ty
    | isValue t -> Just t
    | otherwise -> (\t' -> TmAscribe t' ty) <$> evalStep t

  -- Blame propagates
  TmBlame _ _ -> Nothing

-- =============================================================================
-- Cast Semantics
-- =============================================================================

-- | Apply a cast to a value
--
-- This implements the cast calculus semantics.
-- Key rules:
--   <T => T> v = v                           (identity)
--   <? => G> <G => ?> v = v                  (ground round-trip)
--   <? => G> <G' => ?> v = blame^l           (ground mismatch)
--   <T1->T2 => ?> v = <(T1->T2) => (?->?)> v (function to dyn)
applyCast :: Term -> Type -> Type -> BlameLabel -> Maybe Term
applyCast v ty1 ty2 l
  -- Identity cast
  | ty1 == ty2 = Just v

  -- Cast to dynamic: go through ground type
  | ty2 == TyDyn =
    if isGround ty1
      then Nothing  -- Already at ground, value form
      else case groundOf ty1 of
        Just g -> Just $ TmCast (TmCast v ty1 g l) g TyDyn l
        Nothing -> Nothing

  -- Cast from dynamic: go through ground type
  | ty1 == TyDyn =
    case v of
      TmCast v' ty1' _ _ | ty1' == TyDyn ->
        -- <G => ?> v is wrapped
        case groundOf ty2 of
          Just g ->
            if ty1' == g || (isFunTy ty1' && isFunTy ty2)
              then Just $ TmCast v' ty1' ty2 l
              else Just $ TmBlame ty2 l  -- Ground mismatch!
          Nothing -> Just $ TmBlame ty2 l
      _ ->
        if isGround ty2
          then Nothing  -- Need to unwrap first
          else case groundOf ty2 of
            Just g -> Just $ TmCast (TmCast v TyDyn g l) g ty2 l
            Nothing -> Nothing

  -- Function cast: defer to application
  | TyFun _ _ <- ty1, TyFun _ _ <- ty2 =
    Nothing  -- Cast is value form, applied at application site

  -- Other casts: check compatibility
  | otherwise =
    if isBaseType ty1 && isBaseType ty2 && ty1 == ty2
      then Just v
      else Just $ TmBlame ty2 l

-- | Get the ground type for a type
groundOf :: Type -> Maybe Type
groundOf TyBool = Just TyBool
groundOf TyNat = Just TyNat
groundOf TyUnit = Just TyUnit
groundOf (TyFun _ _) = Just (TyFun TyDyn TyDyn)
groundOf TyDyn = Nothing

-- | Check if a type is a function type
isFunTy :: Type -> Bool
isFunTy (TyFun _ _) = True
isFunTy _ = False
