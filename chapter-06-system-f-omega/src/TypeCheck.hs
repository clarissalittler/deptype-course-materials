{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( KindCtx, TypeCtx
  , kinding, typeOf, typeCheck
  , TypeError(..)
  ) where

import Syntax
import Eval (normalizeType)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Monad (unless)

-- | Kind context: maps type variables to their kinds
type KindCtx = Map TyVar Kind

-- | Type context: maps term variables to their types
type TypeCtx = Map Var Type

-- | Type checking errors
data TypeError
  = UnboundVariable Var
  | UnboundTypeVariable TyVar
  | TypeMismatch Type Type
  | NotAFunctionType Type
  | NotAForallType Type
  | KindMismatch Kind Kind
  | NotATypeOperator Type
  | IllKinded Type
  deriving (Eq, Show)

-- | Kinding judgment: Γ ⊢ τ :: κ
-- Checks that type τ has kind κ under kind context Γ
kinding :: KindCtx -> Type -> Either TypeError Kind
kinding kctx = \case
  -- Variable: look up in kind context
  TyVar a ->
    case Map.lookup a kctx of
      Just k -> Right k
      Nothing -> Left (UnboundTypeVariable a)

  -- Function type: both argument and result must have kind *
  TyArr t1 t2 -> do
    k1 <- kinding kctx t1
    k2 <- kinding kctx t2
    unless (k1 == KStar) $ Left (KindMismatch KStar k1)
    unless (k2 == KStar) $ Left (KindMismatch KStar k2)
    return KStar

  -- Universal quantification: body must have kind * under extended context
  TyForall a k t -> do
    k' <- kinding (Map.insert a k kctx) t
    unless (k' == KStar) $ Left (KindMismatch KStar k')
    return KStar

  -- Type lambda: λα::κ₁. τ has kind κ₁ → κ₂ if τ::κ₂ under α::κ₁
  TyLam a k1 t -> do
    k2 <- kinding (Map.insert a k1 kctx) t
    return (KArr k1 k2)

  -- Type application: if t1 :: κ₁ → κ₂ and t2 :: κ₁, then (t1 t2) :: κ₂
  TyApp t1 t2 -> do
    k1 <- kinding kctx t1
    k2 <- kinding kctx t2
    case k1 of
      KArr kArg kRes -> do
        unless (k2 == kArg) $ Left (KindMismatch kArg k2)
        return kRes
      _ -> Left (NotATypeOperator t1)

  -- Base types have kind *
  TyBool -> Right KStar
  TyNat -> Right KStar

-- | Type checking: Γ; Δ ⊢ t : τ
-- Infers the type of term t under kind context Γ and type context Δ
typeOf :: KindCtx -> TypeCtx -> Term -> Either TypeError Type
typeOf kctx ctx = \case
  -- Variable: look up in type context
  Var x ->
    case Map.lookup x ctx of
      Just ty -> Right ty
      Nothing -> Left (UnboundVariable x)

  -- Lambda: check parameter type is well-kinded, then check body
  Lam x ty t -> do
    k <- kinding kctx ty
    unless (k == KStar) $ Left (IllKinded ty)
    bodyTy <- typeOf kctx (Map.insert x ty ctx) t
    return (TyArr ty bodyTy)

  -- Application: check function and argument types match
  App t1 t2 -> do
    ty1 <- typeOf kctx ctx t1
    ty2 <- typeOf kctx ctx t2
    case normalizeType ty1 of
      TyArr argTy resTy -> do
        unless (typesEqual ty2 argTy) $ Left (TypeMismatch argTy ty2)
        return resTy
      _ -> Left (NotAFunctionType (normalizeType ty1))

  -- Type abstraction: check body under extended kind context
  TyAbs a k t -> do
    bodyTy <- typeOf (Map.insert a k kctx) ctx t
    return (TyForall a k bodyTy)

  -- Type application: instantiate forall type with argument
  TyAppTerm t ty -> do
    termTy <- typeOf kctx ctx t
    case normalizeType termTy of
      TyForall a k body -> do
        tyKind <- kinding kctx ty
        unless (tyKind == k) $ Left (KindMismatch k tyKind)
        return (normalizeType (substTyVarType a ty body))
      _ -> Left (NotAForallType (normalizeType termTy))

  -- Boolean literals
  TmTrue -> Right TyBool
  TmFalse -> Right TyBool

  -- Conditional: guard must be Bool, branches must have same type
  TmIf t1 t2 t3 -> do
    ty1 <- typeOf kctx ctx t1
    ty2 <- typeOf kctx ctx t2
    ty3 <- typeOf kctx ctx t3
    unless (typesEqual ty1 TyBool) $ Left (TypeMismatch TyBool ty1)
    unless (typesEqual ty2 ty3) $ Left (TypeMismatch ty2 ty3)
    return ty2

  -- Natural number literals and operations
  TmZero -> Right TyNat

  TmSucc t -> do
    ty <- typeOf kctx ctx t
    unless (typesEqual ty TyNat) $ Left (TypeMismatch TyNat ty)
    return TyNat

  TmPred t -> do
    ty <- typeOf kctx ctx t
    unless (typesEqual ty TyNat) $ Left (TypeMismatch TyNat ty)
    return TyNat

  TmIsZero t -> do
    ty <- typeOf kctx ctx t
    unless (typesEqual ty TyNat) $ Left (TypeMismatch TyNat ty)
    return TyBool

-- | Type check a term against an expected type
typeCheck :: KindCtx -> TypeCtx -> Term -> Type -> Either TypeError ()
typeCheck kctx ctx t expected = do
  actual <- typeOf kctx ctx t
  unless (typesEqual actual expected) $ Left (TypeMismatch expected actual)

typesEqual :: Type -> Type -> Bool
typesEqual t1 t2 = normalizeType t1 == normalizeType t2
