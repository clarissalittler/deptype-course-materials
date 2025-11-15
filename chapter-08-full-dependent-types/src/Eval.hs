{-# LANGUAGE LambdaCase #-}

module Eval
  ( Value
  , eval
  , normalize
  , isValue
  , matchPattern
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- | Values (normal forms)
type Value = Term

-- | Check if a term is a value
isValue :: Term -> Bool
isValue = \case
  Universe _ -> True
  Lam {} -> True
  Pi {} -> True
  Sigma {} -> True
  Pair v1 v2 -> isValue v1 && isValue v2
  Nat -> True
  Zero -> True
  Succ v -> isValue v
  Bool -> True
  TmTrue -> True
  TmFalse -> True
  Unit -> True
  TT -> True
  Empty -> True
  Refl v -> isValue v
  Eq a x y -> isValue a && isValue x && isValue y
  Con name vs -> all isValue vs
  Ind _ -> True
  _ -> False

-- | Pattern matching
-- Returns Just (bindings) if match succeeds, Nothing otherwise
matchPattern :: Pattern -> Term -> Maybe (Map Name Term)
matchPattern = go
  where
    go :: Pattern -> Term -> Maybe (Map Name Term)
    go PWild _ = Just Map.empty
    go (PVar x) t = Just (Map.singleton x t)
    go (PCon c1 pats) (Con c2 ts)
      | c1 == c2 && length pats == length ts = do
          bindings <- mapM (uncurry go) (zip pats ts)
          return (Map.unions bindings)
      | otherwise = Nothing
    go (PCon _ _) _ = Nothing

-- | Apply bindings from pattern matching
applyBindings :: Map Name Term -> Term -> Term
applyBindings bindings t = Map.foldrWithKey subst t bindings

-- | Single-step evaluation
step :: Term -> Maybe Term
step = \case
  -- Beta reduction for lambda
  App (Lam x _ t) v | isValue v -> Just (subst x v t)

  -- Reduce function in application
  App t1 t2 | not (isValue t1) ->
    App <$> step t1 <*> pure t2

  -- Reduce argument in application
  App v1 t2 | isValue v1, not (isValue t2) ->
    App v1 <$> step t2

  -- Pair projections
  Fst (Pair v1 _) | isValue v1 -> Just v1
  Fst t | not (isValue t) -> Fst <$> step t

  Snd (Pair _ v2) | isValue v2 -> Just v2
  Snd t | not (isValue t) -> Snd <$> step t

  -- Reduce inside pairs
  Pair t1 t2 | not (isValue t1) ->
    Pair <$> step t1 <*> pure t2
  Pair v1 t2 | isValue v1, not (isValue t2) ->
    Pair v1 <$> step t2

  -- Pattern matching
  Match v branches | isValue v -> tryMatch v branches
  Match t branches | not (isValue t) ->
    (\t' -> Match t' branches) <$> step t

  -- Nat eliminator
  -- natElim P z s Zero → z
  NatElim _ z _ Zero -> Just z

  -- natElim P z s (Succ n) → s n (natElim P z s n)
  NatElim p z s (Succ n) | isValue n ->
    Just (App (App s n) (NatElim p z s n))

  -- Reduce scrutinee
  NatElim p z s n | not (isValue n) ->
    (\n' -> NatElim p z s n') <$> step n

  -- Bool eliminator
  -- boolElim P t f True → t
  BoolElim _ t _ TmTrue -> Just t

  -- boolElim P t f False → f
  BoolElim _ _ f TmFalse -> Just f

  -- Reduce scrutinee
  BoolElim p t f b | not (isValue b) ->
    (\b' -> BoolElim p t f b') <$> step b

  -- Unit eliminator
  -- unitElim P u TT → u
  UnitElim _ u TT -> Just u

  -- Reduce scrutinee
  UnitElim p u x | not (isValue x) ->
    (\x' -> UnitElim p u x') <$> step x

  -- Empty eliminator (no reduction rule - no values of Empty type)
  EmptyElim p e | not (isValue e) ->
    (\e' -> EmptyElim p e') <$> step e

  -- Equality eliminator J
  -- J A C p x x (refl x) → p
  J _ _ p x y (Refl z) | isValue x, isValue y, isValue z, alphaEq x y && alphaEq y z ->
    Just p

  -- Reduce arguments
  J a c p x y eq | not (isValue eq) ->
    (\eq' -> J a c p x y eq') <$> step eq

  -- Successor
  Succ t | not (isValue t) -> Succ <$> step t

  -- Reduce inside dependent types (when they appear as terms)
  Pi x a b | not (isValue a) ->
    Pi x <$> step a <*> pure b

  Sigma x a b | not (isValue a) ->
    Sigma x <$> step a <*> pure b

  -- No reduction possible
  _ -> Nothing

-- | Try to match against branches
tryMatch :: Term -> [(Pattern, Term)] -> Maybe Term
tryMatch _ [] = Nothing
tryMatch v ((pat, rhs):rest) =
  case matchPattern pat v of
    Just bindings -> Just (applyBindings bindings rhs)
    Nothing -> tryMatch v rest

-- | Evaluate to normal form
eval :: Term -> Term
eval t = case step t of
  Just t' -> eval t'
  Nothing -> t

-- | Normalize a term (same as eval for this implementation)
normalize :: Term -> Term
normalize = eval
