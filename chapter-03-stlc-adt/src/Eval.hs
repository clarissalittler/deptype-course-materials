{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Eval
  ( -- * Values
    isValue
  , isNumericValue
    -- * Evaluation
  , step
  , eval
  , normalize
    -- * Pattern matching
  , matchPattern
  , Substitution
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- | Substitution environment for pattern matching
type Substitution = Map Var Term

-- | Check if a term is a value
isValue :: Term -> Bool
isValue = \case
  Lam _ _ _ -> True
  TmTrue -> True
  TmFalse -> True
  TmUnit -> True
  TmPair v1 v2 -> isValue v1 && isValue v2
  TmInl _ v -> isValue v
  TmInr _ v -> isValue v
  TmRecord fields -> all isValue (Map.elems fields)
  TmTag _ v _ -> isValue v
  TmNil _ -> True
  TmCons v vs -> isValue v && isValue vs
  t | isNumericValue t -> True
  _ -> False

-- | Check if a term is a numeric value
isNumericValue :: Term -> Bool
isNumericValue = \case
  TmZero -> True
  TmSucc t -> isNumericValue t
  _ -> False

-- | Single-step evaluation (call-by-value)
step :: Term -> Maybe Term
step = \case
  Var _ -> Nothing
  Lam _ _ _ -> Nothing

  -- Application
  App (Lam x _ t) v | isValue v -> Just (substVar x v t)
  App t1 t2
    | not (isValue t1) -> App <$> step t1 <*> pure t2
    | not (isValue t2) -> App t1 <$> step t2
    | otherwise -> Nothing

  -- Booleans
  TmTrue -> Nothing
  TmFalse -> Nothing
  TmIf TmTrue t2 _ -> Just t2
  TmIf TmFalse _ t3 -> Just t3
  TmIf t1 t2 t3 -> (\t1' -> TmIf t1' t2 t3) <$> step t1

  -- Natural numbers
  TmZero -> Nothing
  TmSucc t -> TmSucc <$> step t
  TmPred TmZero -> Just TmZero
  TmPred (TmSucc nv) | isNumericValue nv -> Just nv
  TmPred t -> TmPred <$> step t
  TmIsZero TmZero -> Just TmTrue
  TmIsZero (TmSucc nv) | isNumericValue nv -> Just TmFalse
  TmIsZero t -> TmIsZero <$> step t

  -- Unit
  TmUnit -> Nothing

  -- Products
  TmPair t1 t2
    | not (isValue t1) -> TmPair <$> step t1 <*> pure t2
    | not (isValue t2) -> TmPair t1 <$> step t2
    | otherwise -> Nothing

  TmFst (TmPair v1 _) | isValue v1 -> Just v1
  TmFst t -> TmFst <$> step t

  TmSnd (TmPair _ v2) | isValue v2 -> Just v2
  TmSnd t -> TmSnd <$> step t

  -- Sums
  TmInl ty t
    | not (isValue t) -> TmInl ty <$> step t
    | otherwise -> Nothing

  TmInr ty t
    | not (isValue t) -> TmInr ty <$> step t
    | otherwise -> Nothing

  TmCase (TmInl _ v) x1 t1 _ _
    | isValue v -> Just (substVar x1 v t1)
  TmCase (TmInr _ v) _ _ x2 t2
    | isValue v -> Just (substVar x2 v t2)
  TmCase t x1 t1 x2 t2 -> (\t' -> TmCase t' x1 t1 x2 t2) <$> step t

  -- Records
  TmRecord fields
    | all isValue (Map.elems fields) -> Nothing
    | otherwise ->
        let stepField (l, t)
              | isValue t = Nothing
              | otherwise = (l,) <$> step t
        in case findFirst stepField (Map.toList fields) of
          Just (l, t') -> Just (TmRecord (Map.insert l t' fields))
          Nothing -> Nothing

  TmProj (TmRecord fields) label
    | all isValue (Map.elems fields) ->
        Map.lookup label fields
    | otherwise -> Nothing
  TmProj t label -> (\t' -> TmProj t' label) <$> step t

  -- Variants
  TmTag label t ty
    | not (isValue t) -> TmTag label <$> step t <*> pure ty
    | otherwise -> Nothing

  TmCaseVariant (TmTag label v varTy) cases
    | isValue v ->
        case lookupVariantCase label cases of
          Just (x, body) -> Just (substVar x v body)
          Nothing -> Nothing
    | otherwise -> Nothing
  TmCaseVariant t cases ->
    (\t' -> TmCaseVariant t' cases) <$> step t

  -- Lists
  TmNil _ -> Nothing

  TmCons t1 t2
    | not (isValue t1) -> TmCons <$> step t1 <*> pure t2
    | not (isValue t2) -> TmCons t1 <$> step t2
    | otherwise -> Nothing

  TmIsNil (TmNil _) -> Just TmTrue
  TmIsNil (TmCons _ _) -> Just TmFalse
  TmIsNil t -> TmIsNil <$> step t

  TmHead (TmCons v _) | isValue v -> Just v
  TmHead t -> TmHead <$> step t

  TmTail (TmCons _ vs) | isValue vs -> Just vs
  TmTail t -> TmTail <$> step t

  -- Pattern matching
  TmMatch v cases | isValue v ->
    tryPatterns v cases
  TmMatch t cases ->
    (\t' -> TmMatch t' cases) <$> step t

-- | Try to match value against patterns
tryPatterns :: Term -> [(Pattern, Term)] -> Maybe Term
tryPatterns _ [] = Nothing
tryPatterns v ((pat, body):rest) =
  case matchPattern pat v of
    Just subst -> Just (applySubst subst body)
    Nothing -> tryPatterns v rest

-- | Match a pattern against a value
matchPattern :: Pattern -> Term -> Maybe Substitution
matchPattern pat val = case (pat, val) of
  (PatVar x, v) -> Just (Map.singleton x v)
  (PatWild, _) -> Just Map.empty
  (PatUnit, TmUnit) -> Just Map.empty
  (PatTrue, TmTrue) -> Just Map.empty
  (PatFalse, TmFalse) -> Just Map.empty
  (PatZero, TmZero) -> Just Map.empty
  (PatSucc p, TmSucc v) -> matchPattern p v
  (PatPair p1 p2, TmPair v1 v2) -> do
    subst1 <- matchPattern p1 v1
    subst2 <- matchPattern p2 v2
    Just (Map.union subst1 subst2)
  (PatInl p, TmInl _ v) -> matchPattern p v
  (PatInr p, TmInr _ v) -> matchPattern p v
  (PatVariant label p, TmTag label' v _)
    | label == label' -> matchPattern p v
  (PatNil, TmNil _) -> Just Map.empty
  (PatCons p ps, TmCons v vs) -> do
    subst1 <- matchPattern p v
    subst2 <- matchPattern ps vs
    Just (Map.union subst1 subst2)
  _ -> Nothing

-- | Apply a substitution to a term
applySubst :: Substitution -> Term -> Term
applySubst subst = go
  where
    go t@(Var x) = Map.findWithDefault t x subst
    go (Lam x ty body)
      | x `Map.member` subst = Lam x ty body  -- Don't substitute bound vars
      | otherwise = Lam x ty (go body)
    go (App t1 t2) = App (go t1) (go t2)
    go TmTrue = TmTrue
    go TmFalse = TmFalse
    go (TmIf t1 t2 t3) = TmIf (go t1) (go t2) (go t3)
    go TmZero = TmZero
    go (TmSucc t) = TmSucc (go t)
    go (TmPred t) = TmPred (go t)
    go (TmIsZero t) = TmIsZero (go t)
    go TmUnit = TmUnit
    go (TmPair t1 t2) = TmPair (go t1) (go t2)
    go (TmFst t) = TmFst (go t)
    go (TmSnd t) = TmSnd (go t)
    go (TmInl ty t) = TmInl ty (go t)
    go (TmInr ty t) = TmInr ty (go t)
    go (TmCase t x1 t1 x2 t2) =
      TmCase (go t)
        x1 (if x1 `Map.member` subst then t1 else go t1)
        x2 (if x2 `Map.member` subst then t2 else go t2)
    go (TmRecord fields) = TmRecord (fmap go fields)
    go (TmProj t label) = TmProj (go t) label
    go (TmTag label t ty) = TmTag label (go t) ty
    go (TmCaseVariant t cases) =
      TmCaseVariant (go t)
        [(l, x, if x `Map.member` subst then ti else go ti) | (l, x, ti) <- cases]
    go (TmNil ty) = TmNil ty
    go (TmCons t1 t2) = TmCons (go t1) (go t2)
    go (TmIsNil t) = TmIsNil (go t)
    go (TmHead t) = TmHead (go t)
    go (TmTail t) = TmTail (go t)
    go (TmMatch t cases) = TmMatch (go t) cases  -- Pattern vars handled separately

-- | Normalize to a value
normalize :: Term -> Term
normalize = go (1000 :: Int)
  where
    go 0 t = t
    go n t = case step t of
      Nothing -> t
      Just t' -> go (n - 1) t'

-- | Evaluate (same as normalize)
eval :: Term -> Term
eval = normalize

-- | Lookup in variant case list
lookupVariantCase :: Label -> [(Label, Var, Term)] -> Maybe (Var, Term)
lookupVariantCase _ [] = Nothing
lookupVariantCase l ((l', x, t):rest)
  | l == l' = Just (x, t)
  | otherwise = lookupVariantCase l rest

-- | Find first Just value in a list
findFirst :: (a -> Maybe b) -> [a] -> Maybe b
findFirst _ [] = Nothing
findFirst f (x:xs) = case f x of
  Just y -> Just y
  Nothing -> findFirst f xs
