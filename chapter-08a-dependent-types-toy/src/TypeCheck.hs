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
  | UniverseMismatch Level Level
  | PatternMatchError String
  | NotAnInductive Term
  deriving (Eq, Show)

-- | Check if two types are equal (up to normalization and alpha equivalence)
typeEq :: Term -> Term -> Bool
typeEq t1 t2 = alphaEq (normalize t1) (normalize t2)

-- | Infer the type of a term
typeOf :: Context -> Term -> Either TypeError Term
typeOf ctx = \case
  -- Universe hierarchy: Type i : Type (i+1)
  Universe i -> Right (Universe (i + 1))

  -- Variable: look up in context
  Var x -> case Map.lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left (UnboundVariable x)

  -- Lambda: λ(x:A). t
  Lam x a t -> do
    aType <- typeOf ctx a
    case normalize aType of
      Universe _ -> do
        b <- typeOf (extendCtx x a ctx) t
        return (Pi x a b)
      _ -> Left (NotAType a)

  -- Application: t₁ t₂
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
  Pi x a b -> do
    aType <- typeOf ctx a
    bType <- typeOf (extendCtx x a ctx) b
    case (normalize aType, normalize bType) of
      (Universe i, Universe j) -> return (Universe (max i j))
      (Universe _, _) -> Left (NotAType b)
      _ -> Left (NotAType a)

  -- Sigma type: Σ(x:A). B
  Sigma x a b -> do
    aType <- typeOf ctx a
    bType <- typeOf (extendCtx x a ctx) b
    case (normalize aType, normalize bType) of
      (Universe i, Universe j) -> return (Universe (max i j))
      (Universe _, _) -> Left (NotAType b)
      _ -> Left (NotAType a)

  -- Pair: (t₁, t₂)
  Pair t1 t2 -> do
    ty1 <- typeOf ctx t1
    ty2 <- typeOf ctx t2
    let x = freshName "x" (freeVars ty1 `Set.union` freeVars ty2)
    return (Sigma x ty1 ty2)

  -- First projection: fst t
  Fst t -> do
    ty <- typeOf ctx t
    case normalize ty of
      Sigma _ a _ -> return a
      _ -> Left (NotASigma ty)

  -- Second projection: snd t
  Snd t -> do
    ty <- typeOf ctx t
    case normalize ty of
      Sigma x _ b -> return (subst x (Fst t) b)
      _ -> Left (NotASigma ty)

  -- Inductive type reference
  Ind _ -> Right (Universe 0)  -- Simplification: all inductive types in Type 0

  -- Constructor application (simplified)
  Con name args -> do
    -- In a full implementation, we'd look up the constructor type
    -- For simplicity, we'll infer based on known constructors
    case (name, args) of
      ("Nil", [ty]) -> do
        tyType <- typeOf ctx ty
        case normalize tyType of
          Universe _ -> return (App (App (Ind "Vec") ty) Zero)
          _ -> Left (NotAType ty)
      ("Cons", [ty, n, x, xs]) -> do
        -- Check types
        _ <- typeOf ctx ty
        _ <- typeOf ctx n
        _ <- typeOf ctx x
        _ <- typeOf ctx xs
        return (App (App (Ind "Vec") ty) (Succ n))
      _ -> Left (PatternMatchError $ "Unknown constructor: " ++ name)

  -- Pattern matching
  Match scrutinee branches -> do
    _ <- typeOf ctx scrutinee
    case branches of
      [] -> Left (PatternMatchError "Empty pattern match")
      ((_, rhs):_) -> do
        -- For simplicity, assume all branches have the same type
        -- In a real implementation, we'd check all branches
        typeOf ctx rhs

  -- Equality type: Eq A x y
  Eq a x y -> do
    aType <- typeOf ctx a
    xType <- typeOf ctx x
    yType <- typeOf ctx y
    case normalize aType of
      Universe i -> do
        if typeEq a xType && typeEq a yType
          then return (Universe i)
          else Left (TypeMismatch a xType)
      _ -> Left (NotAType a)

  -- Reflexivity: refl x
  Refl x -> do
    xType <- typeOf ctx x
    return (Eq xType x x)

  -- J eliminator
  J a c _p x y eq -> do
    -- Simplified type checking for J
    -- Full version would check:
    -- a : Type, c : Π(z:a). Π(e:x=z). Type
    -- p : c x (refl x), x : a, y : a, eq : x = y
    -- Result: c y eq
    eqType <- typeOf ctx eq
    case normalize eqType of
      Eq _ x' y' | typeEq x x' && typeEq y y' ->
        return (App (App c y) eq)
      _ -> Left (TypeMismatch (Eq a x y) eqType)

  -- Natural numbers
  Nat -> Right (Universe 0)
  Zero -> Right Nat
  Succ t -> do
    ty <- typeOf ctx t
    if typeEq ty Nat
      then return Nat
      else Left (TypeMismatch Nat ty)

  -- Nat eliminator: natElim(P, z, s, n)
  NatElim p z s n -> do
    -- P : Nat → Type
    _ <- typeOf ctx p
    -- z : P 0
    _ <- typeOf ctx z
    -- s : Π(k:Nat). P k → P (succ k)
    _ <- typeOf ctx s
    -- n : Nat
    nType <- typeOf ctx n

    if typeEq nType Nat
      then return (App p n)
      else Left (TypeMismatch Nat nType)

  -- Booleans
  Bool -> Right (Universe 0)
  TmTrue -> Right Bool
  TmFalse -> Right Bool

  -- Bool eliminator
  BoolElim p _t _f b -> do
    bType <- typeOf ctx b
    if typeEq bType Bool
      then return (App p b)
      else Left (TypeMismatch Bool bType)

  -- Unit type
  Unit -> Right (Universe 0)
  TT -> Right Unit

  -- Unit eliminator
  UnitElim p _u x -> do
    xType <- typeOf ctx x
    if typeEq xType Unit
      then return (App p x)
      else Left (TypeMismatch Unit xType)

  -- Empty type
  Empty -> Right (Universe 0)

  -- Empty eliminator (ex falso quodlibet)
  EmptyElim p e -> do
    eType <- typeOf ctx e
    if typeEq eType Empty
      then typeOf ctx p  -- Can produce any type from Empty
      else Left (TypeMismatch Empty eType)

-- | Check that a term has a given type
typeCheck :: Context -> Term -> Term -> Either TypeError ()
typeCheck ctx t expected = do
  actual <- typeOf ctx t
  if typeEq expected actual
    then return ()
    else Left (TypeMismatch expected actual)
