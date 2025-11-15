{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( TypeError(..)
  , TypeContext
  , typeOf
  , typeCheck
  , emptyContext
  , extendContext
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Monad (unless)

-- | Type checking context (Γ): maps variables to their types
type TypeContext = Map Var Type

-- | Empty type context
emptyContext :: TypeContext
emptyContext = Map.empty

-- | Extend context with a variable binding
extendContext :: Var -> Type -> TypeContext -> TypeContext
extendContext = Map.insert

-- | Type errors
data TypeError
  = UnboundVariable Var
  | TypeMismatch { expected :: Type, actual :: Type }
  | NotAFunction Type
  | ConditionNotBool Type
  | ArgumentTypeMismatch { paramType :: Type, argType :: Type }
  | NotANat Type
  deriving (Eq, Show)

-- | Infer the type of a term in a given context
-- Returns Left with an error if the term is not well-typed
typeOf :: TypeContext -> Term -> Either TypeError Type
typeOf ctx = \case
  -- T-Var: look up variable in context
  Var x ->
    case Map.lookup x ctx of
      Just ty -> Right ty
      Nothing -> Left (UnboundVariable x)

  -- T-Abs: λ(x:T₁). t₂ has type T₁ → T₂ if t₂ has type T₂ under context Γ,x:T₁
  Lam x ty t -> do
    let ctx' = extendContext x ty ctx
    tyBody <- typeOf ctx' t
    return $ TyArr ty tyBody

  -- T-App: t₁ t₂ has type T₂ if t₁ has type T₁→T₂ and t₂ has type T₁
  App t1 t2 -> do
    ty1 <- typeOf ctx t1
    ty2 <- typeOf ctx t2
    case ty1 of
      TyArr tyParam tyResult -> do
        unless (tyParam == ty2) $
          Left (ArgumentTypeMismatch tyParam ty2)
        return tyResult
      _ -> Left (NotAFunction ty1)

  -- T-True
  TmTrue -> Right TyBool

  -- T-False
  TmFalse -> Right TyBool

  -- T-If: if t₁ then t₂ else t₃ has type T if:
  --   - t₁ has type Bool
  --   - t₂ and t₃ both have type T
  TmIf t1 t2 t3 -> do
    ty1 <- typeOf ctx t1
    unless (ty1 == TyBool) $
      Left (ConditionNotBool ty1)
    ty2 <- typeOf ctx t2
    ty3 <- typeOf ctx t3
    unless (ty2 == ty3) $
      Left (TypeMismatch ty2 ty3)
    return ty2

  -- T-Zero
  TmZero -> Right TyNat

  -- T-Succ: succ t has type Nat if t has type Nat
  TmSucc t -> do
    ty <- typeOf ctx t
    unless (ty == TyNat) $
      Left (NotANat ty)
    return TyNat

  -- T-Pred: pred t has type Nat if t has type Nat
  TmPred t -> do
    ty <- typeOf ctx t
    unless (ty == TyNat) $
      Left (NotANat ty)
    return TyNat

  -- T-IsZero: iszero t has type Bool if t has type Nat
  TmIsZero t -> do
    ty <- typeOf ctx t
    unless (ty == TyNat) $
      Left (NotANat ty)
    return TyBool

-- | Type check a closed term (no free variables)
typeCheck :: Term -> Either TypeError Type
typeCheck = typeOf emptyContext
