{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( Context
  , TypeError(..)
  , typeOf
  , typeCheck
  , emptyCtx
  , extendCtx
  ) where

import Syntax
import Eval
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set

-- | Type context: maps variables to their types
type Context = Map Name Term

-- | Empty context
emptyCtx :: Context
emptyCtx = Map.empty

-- | Extend context with a new binding
extendCtx :: Name -> Term -> Context -> Context
extendCtx = Map.insert

-- | Type checking errors
data TypeError
  = UnboundVariable Name
  | TypeMismatch Term Term  -- expected, actual
  | NotAFunction Term
  | NotAPi Term
  | NotASigma Term
  | NotAType Term
  | InvalidUniverse
  deriving (Eq, Show)

-- | Check if two types are equal (up to normalization and alpha equivalence)
typeEq :: Term -> Term -> Bool
typeEq t1 t2 = alphaEq (normalize t1) (normalize t2)

-- | Infer the type of a term
typeOf :: Context -> Term -> Either TypeError Term
typeOf ctx = \case
  -- Universe: Type : Type (we use Type-in-Type for simplicity, though it's inconsistent)
  Type -> Right Type

  -- Variable: look up in context
  Var x -> case Map.lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left (UnboundVariable x)

  -- Lambda: λ(x:A). t
  -- Check: Γ ⊢ A : Type
  --        Γ, x:A ⊢ t : B
  -- Infer: Γ ⊢ λ(x:A). t : Π(x:A). B
  Lam x a t -> do
    aType <- typeOf ctx a
    case normalize aType of
      Type -> do
        b <- typeOf (extendCtx x a ctx) t
        return (Pi x a b)
      _ -> Left (NotAType a)

  -- Application: t₁ t₂
  -- Check: Γ ⊢ t₁ : Π(x:A). B
  --        Γ ⊢ t₂ : A
  -- Infer: Γ ⊢ t₁ t₂ : [x ↦ t₂]B
  App t1 t2 -> do
    ty1 <- typeOf ctx t1
    case normalize ty1 of
      Pi x a b -> do
        ty2 <- typeOf ctx t2
        if typeEq a ty2
          then return (subst x t2 b)
          else Left (TypeMismatch a ty2)
      _ -> Left (NotAPi ty1)

  -- Pi type: Π(x:A). B
  -- Check: Γ ⊢ A : Type
  --        Γ, x:A ⊢ B : Type
  -- Infer: Γ ⊢ Π(x:A). B : Type
  Pi x a b -> do
    aType <- typeOf ctx a
    bType <- typeOf (extendCtx x a ctx) b
    case (normalize aType, normalize bType) of
      (Type, Type) -> return Type
      (Type, _) -> Left (NotAType b)
      _ -> Left (NotAType a)

  -- Sigma type: Σ(x:A). B
  -- Check: Γ ⊢ A : Type
  --        Γ, x:A ⊢ B : Type
  -- Infer: Γ ⊢ Σ(x:A). B : Type
  Sigma x a b -> do
    aType <- typeOf ctx a
    bType <- typeOf (extendCtx x a ctx) b
    case (normalize aType, normalize bType) of
      (Type, Type) -> return Type
      (Type, _) -> Left (NotAType b)
      _ -> Left (NotAType a)

  -- Pair: (t₁, t₂)
  -- Check: Γ ⊢ t₁ : A
  --        Γ ⊢ t₂ : [x ↦ t₁]B
  -- Infer: Γ ⊢ (t₁, t₂) : Σ(x:A). B
  -- Note: We need to infer the Sigma type, which is tricky
  -- For simplicity, we require type annotation elsewhere
  Pair t1 t2 -> do
    ty1 <- typeOf ctx t1
    ty2 <- typeOf ctx t2
    -- Return a Sigma type with a fresh variable
    let x = freshName "x" (freeVars ty1 `Set.union` freeVars ty2)
    return (Sigma x ty1 ty2)

  -- First projection: fst t
  -- Check: Γ ⊢ t : Σ(x:A). B
  -- Infer: Γ ⊢ fst t : A
  Fst t -> do
    ty <- typeOf ctx t
    case normalize ty of
      Sigma _ a _ -> return a
      _ -> Left (NotASigma ty)

  -- Second projection: snd t
  -- Check: Γ ⊢ t : Σ(x:A). B
  -- Infer: Γ ⊢ snd t : [x ↦ fst t]B
  Snd t -> do
    ty <- typeOf ctx t
    case normalize ty of
      Sigma x _ b -> return (subst x (Fst t) b)
      _ -> Left (NotASigma ty)

  -- Natural numbers
  Nat -> Right Type
  Zero -> Right Nat
  Succ t -> do
    ty <- typeOf ctx t
    if typeEq ty Nat
      then return Nat
      else Left (TypeMismatch Nat ty)

  -- Booleans
  Bool -> Right Type
  TmTrue -> Right Bool
  TmFalse -> Right Bool

  If t1 t2 t3 -> do
    ty1 <- typeOf ctx t1
    if not (typeEq ty1 Bool)
      then Left (TypeMismatch Bool ty1)
      else do
        ty2 <- typeOf ctx t2
        ty3 <- typeOf ctx t3
        if typeEq ty2 ty3
          then return ty2
          else Left (TypeMismatch ty2 ty3)

-- | Check that a term has a given type
typeCheck :: Context -> Term -> Term -> Either TypeError ()
typeCheck ctx t expected = do
  actual <- typeOf ctx t
  if typeEq expected actual
    then return ()
    else Left (TypeMismatch expected actual)
