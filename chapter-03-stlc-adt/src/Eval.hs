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
import qualified Data.Set as Set
import Data.Set (Set)

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

  TmFst (TmPair v1 v2) | isValue v1 && isValue v2 -> Just v1
  TmFst t -> TmFst <$> step t

  TmSnd (TmPair v1 v2) | isValue v1 && isValue v2 -> Just v2
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

  TmProj t label ->
    case t of
      TmRecord fields
        | all isValue (Map.elems fields) ->
            Map.lookup label fields
      _ -> (\t' -> TmProj t' label) <$> step t

  -- Variants
  TmTag label t ty
    | not (isValue t) -> TmTag label <$> step t <*> pure ty
    | otherwise -> Nothing

  TmCaseVariant t cases ->
    case t of
      TmTag label v _
        | isValue v ->
            case lookupVariantCase label cases of
              Just (x, body) -> Just (substVar x v body)
              Nothing -> Nothing
      _ -> (\t' -> TmCaseVariant t' cases) <$> step t

  -- Lists
  TmNil _ -> Nothing

  TmCons t1 t2
    | not (isValue t1) -> TmCons <$> step t1 <*> pure t2
    | not (isValue t2) -> TmCons t1 <$> step t2
    | otherwise -> Nothing

  TmIsNil (TmNil _) -> Just TmTrue
  TmIsNil (TmCons v vs) | isValue v && isValue vs -> Just TmFalse
  TmIsNil t -> TmIsNil <$> step t

  TmHead (TmCons v vs) | isValue v && isValue vs -> Just v
  TmHead t -> TmHead <$> step t

  TmTail (TmCons v vs) | isValue v && isValue vs -> Just vs
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
applySubst subst = go subst
  where
    go s t@(Var x) = Map.findWithDefault t x s
    go s (Lam x ty body) = Lam x ty (go (Map.delete x s) body)
    go s (App t1 t2) = App (go s t1) (go s t2)
    go _ TmTrue = TmTrue
    go _ TmFalse = TmFalse
    go s (TmIf t1 t2 t3) = TmIf (go s t1) (go s t2) (go s t3)
    go _ TmZero = TmZero
    go s (TmSucc t) = TmSucc (go s t)
    go s (TmPred t) = TmPred (go s t)
    go s (TmIsZero t) = TmIsZero (go s t)
    go _ TmUnit = TmUnit
    go s (TmPair t1 t2) = TmPair (go s t1) (go s t2)
    go s (TmFst t) = TmFst (go s t)
    go s (TmSnd t) = TmSnd (go s t)
    go s (TmInl ty t) = TmInl ty (go s t)
    go s (TmInr ty t) = TmInr ty (go s t)
    go s (TmCase t x1 t1 x2 t2) =
      TmCase (go s t)
        x1 (go (Map.delete x1 s) t1)
        x2 (go (Map.delete x2 s) t2)
    go s (TmRecord fields) = TmRecord (fmap (go s) fields)
    go s (TmProj t label) = TmProj (go s t) label
    go s (TmTag label t ty) = TmTag label (go s t) ty
    go s (TmCaseVariant t cases) =
      TmCaseVariant (go s t)
        [(l, x, go (Map.delete x s) ti) | (l, x, ti) <- cases]
    go _ (TmNil ty) = TmNil ty
    go s (TmCons t1 t2) = TmCons (go s t1) (go s t2)
    go s (TmIsNil t) = TmIsNil (go s t)
    go s (TmHead t) = TmHead (go s t)
    go s (TmTail t) = TmTail (go s t)
    go s (TmMatch t cases) =
      TmMatch (go s t)
        [ (p, go (dropPatternVars s p) ti) | (p, ti) <- cases ]

    dropPatternVars :: Substitution -> Pattern -> Substitution
    dropPatternVars s p = Set.foldr Map.delete s (patternVars p)

    patternVars :: Pattern -> Set Var
    patternVars = \case
      PatVar x -> Set.singleton x
      PatWild -> Set.empty
      PatUnit -> Set.empty
      PatTrue -> Set.empty
      PatFalse -> Set.empty
      PatZero -> Set.empty
      PatSucc p -> patternVars p
      PatPair p1 p2 -> patternVars p1 `Set.union` patternVars p2
      PatInl p -> patternVars p
      PatInr p -> patternVars p
      PatVariant _ p -> patternVars p
      PatNil -> Set.empty
      PatCons p ps -> patternVars p `Set.union` patternVars ps

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
