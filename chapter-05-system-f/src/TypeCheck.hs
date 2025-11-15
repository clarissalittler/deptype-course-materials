{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( TypeError(..)
  , TypeContext, KindContext
  , typeOf, typeCheck
  , emptyTypeCtx, emptyKindCtx
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad (unless)

-- | Type context
type TypeContext = Map.Map Var Type

-- | Kind context (tracks which type variables are in scope)
type KindContext = Set.Set TyVar

-- | Type errors
data TypeError
  = UnboundVariable Var
  | UnboundTypeVariable TyVar
  | TypeMismatch Type Type
  | NotAFunction Type
  | ConditionNotBool Type
  | NotANat Type
  | NotAForall Type
  deriving (Eq, Show)

emptyTypeCtx :: TypeContext
emptyTypeCtx = Map.empty

emptyKindCtx :: KindContext
emptyKindCtx = Set.empty

-- | Type checking for System F
typeOf :: KindContext -> TypeContext -> Term -> Either TypeError Type
typeOf kctx ctx = \case
  -- T-Var
  Var x -> case Map.lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left (UnboundVariable x)

  -- T-Abs
  Lam x ty body -> do
    -- Check that ty is well-formed
    checkTypeWellFormed kctx ty
    tyBody <- typeOf kctx (Map.insert x ty ctx) body
    return $ TyArr ty tyBody

  -- T-App
  App t1 t2 -> do
    ty1 <- typeOf kctx ctx t1
    ty2 <- typeOf kctx ctx t2
    case ty1 of
      TyArr tyParam tyResult -> do
        unless (tyParam == ty2) $
          Left (TypeMismatch tyParam ty2)
        return tyResult
      _ -> Left (NotAFunction ty1)

  -- T-TyAbs (Λα. t)
  TyAbs a t -> do
    let kctx' = Set.insert a kctx
    tyBody <- typeOf kctx' ctx t
    return $ TyForall a tyBody

  -- T-TyApp (t [τ])
  TyApp t ty -> do
    checkTypeWellFormed kctx ty
    tyTerm <- typeOf kctx ctx t
    case tyTerm of
      TyForall a tyBody ->
        return $ substTyVarType a ty tyBody
      _ -> Left (NotAForall tyTerm)

  -- Booleans
  TmTrue -> Right TyBool
  TmFalse -> Right TyBool
  TmIf t1 t2 t3 -> do
    ty1 <- typeOf kctx ctx t1
    unless (ty1 == TyBool) $ Left (ConditionNotBool ty1)
    ty2 <- typeOf kctx ctx t2
    ty3 <- typeOf kctx ctx t3
    unless (ty2 == ty3) $ Left (TypeMismatch ty2 ty3)
    return ty2

  -- Natural numbers
  TmZero -> Right TyNat
  TmSucc t -> do
    ty <- typeOf kctx ctx t
    unless (ty == TyNat) $ Left (NotANat ty)
    return TyNat
  TmPred t -> do
    ty <- typeOf kctx ctx t
    unless (ty == TyNat) $ Left (NotANat ty)
    return TyNat
  TmIsZero t -> do
    ty <- typeOf kctx ctx t
    unless (ty == TyNat) $ Left (NotANat ty)
    return TyBool

-- | Check that a type is well-formed (all type variables are bound)
checkTypeWellFormed :: KindContext -> Type -> Either TypeError ()
checkTypeWellFormed kctx = \case
  TyVar a ->
    unless (a `Set.member` kctx) $ Left (UnboundTypeVariable a)
  TyArr t1 t2 -> do
    checkTypeWellFormed kctx t1
    checkTypeWellFormed kctx t2
  TyForall a t ->
    checkTypeWellFormed (Set.insert a kctx) t
  TyBool -> Right ()
  TyNat -> Right ()

-- | Type check a closed term
typeCheck :: Term -> Either TypeError Type
typeCheck = typeOf emptyKindCtx emptyTypeCtx
