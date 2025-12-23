{-# LANGUAGE LambdaCase #-}
-- | Bidirectional Type Checking
--
-- The key idea: two mutually recursive judgments:
--
--   Γ ⊢ e ⇐ A    "check e against A"   (checking mode)
--   Γ ⊢ e ⇒ A    "infer type A for e"  (inference mode)
--
-- Rule of thumb:
--   - Introduction forms are checked (⇐)
--   - Elimination forms are inferred (⇒)
--   - Annotations switch from checking to inference
--
-- This minimizes needed type annotations while maintaining decidability.

module TypeCheck
  ( -- * Type Checking
    check
  , infer
  , TypeError(..)
    -- * Context
  , Ctx
  , emptyCtx
  , extendCtx
  , lookupCtx
  , extendTyCtx
  ) where

import Control.Monad (unless, when)
import Control.Monad.Except
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Syntax

-- | Type errors
data TypeError
  = UnboundVariable Name
  | UnboundTypeVariable Name
  | TypeMismatch Type Type
  | ExpectedFunction Type
  | ExpectedForall Type
  | ExpectedBool Type
  | ExpectedNat Type
  | ExpectedProduct Type
  | ExpectedSum Type
  | CannotInfer Term
  deriving (Eq, Show)

-- | Typing context
data Ctx = Ctx
  { ctxVars  :: Map.Map Name Type    -- ^ Term variables
  , ctxTyVars :: Set.Set Name        -- ^ Type variables in scope
  } deriving (Eq, Show)

emptyCtx :: Ctx
emptyCtx = Ctx Map.empty Set.empty

extendCtx :: Name -> Type -> Ctx -> Ctx
extendCtx x ty ctx = ctx { ctxVars = Map.insert x ty (ctxVars ctx) }

lookupCtx :: Name -> Ctx -> Maybe Type
lookupCtx x ctx = Map.lookup x (ctxVars ctx)

extendTyCtx :: Name -> Ctx -> Ctx
extendTyCtx a ctx = ctx { ctxTyVars = Set.insert a (ctxTyVars ctx) }

-- | Type checking monad
type TC = Either TypeError

-- | Well-formedness of types
wfType :: Ctx -> Type -> TC ()
wfType ctx = \case
  TyVar a ->
    unless (Set.member a (ctxTyVars ctx)) $
      throwError $ UnboundTypeVariable a
  TyBool -> return ()
  TyNat -> return ()
  TyArr a b -> wfType ctx a >> wfType ctx b
  TyForall a t -> wfType (extendTyCtx a ctx) t
  TyUnit -> return ()
  TyProd a b -> wfType ctx a >> wfType ctx b
  TySum a b -> wfType ctx a >> wfType ctx b

-- | Type equality (for now, syntactic)
typeEq :: Type -> Type -> Bool
typeEq = (==)

-- | Type substitution
substType :: Name -> Type -> Type -> Type
substType a s = \case
  TyVar b | a == b -> s
          | otherwise -> TyVar b
  TyBool -> TyBool
  TyNat -> TyNat
  TyArr t1 t2 -> TyArr (substType a s t1) (substType a s t2)
  TyForall b t | a == b -> TyForall b t  -- Shadowed
               | otherwise -> TyForall b (substType a s t)
  TyUnit -> TyUnit
  TyProd t1 t2 -> TyProd (substType a s t1) (substType a s t2)
  TySum t1 t2 -> TySum (substType a s t1) (substType a s t2)

-- ============================================================
-- INFERENCE MODE (⇒)
-- ============================================================

-- | Infer the type of a term
--
-- Γ ⊢ e ⇒ A
--
-- Returns the inferred type.
infer :: Ctx -> Term -> TC Type
infer ctx = \case
  -- Variables: look up in context
  -- ──────────────────
  -- Γ, x:A ⊢ x ⇒ A
  Var x ->
    case lookupCtx x ctx of
      Just ty -> return ty
      Nothing -> throwError $ UnboundVariable x

  -- Annotated lambda: can infer
  -- Γ, x:A ⊢ e ⇒ B
  -- ─────────────────────────
  -- Γ ⊢ (λx:A. e) ⇒ A → B
  LamAnn x a body -> do
    wfType ctx a
    b <- infer (extendCtx x a ctx) body
    return $ TyArr a b

  -- Application: infer function, check argument
  -- Γ ⊢ e1 ⇒ A → B    Γ ⊢ e2 ⇐ A
  -- ────────────────────────────────
  -- Γ ⊢ e1 e2 ⇒ B
  App e1 e2 -> do
    t1 <- infer ctx e1
    case t1 of
      TyArr a b -> do
        check ctx e2 a
        return b
      _ -> throwError $ ExpectedFunction t1

  -- Annotation: check against annotation, return it
  -- Γ ⊢ e ⇐ A
  -- ─────────────────
  -- Γ ⊢ (e : A) ⇒ A
  Ann e ty -> do
    wfType ctx ty
    check ctx e ty
    return ty

  -- Let: infer bound term, extend context
  Let x e1 e2 -> do
    t1 <- infer ctx e1
    infer (extendCtx x t1 ctx) e2

  -- Booleans are inferrable
  TmTrue -> return TyBool
  TmFalse -> return TyBool

  -- If: infer condition, infer branches, check they match
  If cond thn els -> do
    tcond <- infer ctx cond
    unless (typeEq tcond TyBool) $
      throwError $ ExpectedBool tcond
    tthn <- infer ctx thn
    tels <- infer ctx els
    unless (typeEq tthn tels) $
      throwError $ TypeMismatch tthn tels
    return tthn

  -- Naturals are inferrable
  Zero -> return TyNat
  Suc n -> do
    check ctx n TyNat
    return TyNat

  -- NatRec
  NatRec z s n -> do
    tz <- infer ctx z
    check ctx s (TyArr TyNat (TyArr tz tz))
    check ctx n TyNat
    return tz

  -- Unit
  TmUnit -> return TyUnit

  -- Fst/Snd: infer product, extract component
  Fst e -> do
    t <- infer ctx e
    case t of
      TyProd a _ -> return a
      _ -> throwError $ ExpectedProduct t

  Snd e -> do
    t <- infer ctx e
    case t of
      TyProd _ b -> return b
      _ -> throwError $ ExpectedProduct t

  -- Case: infer scrutinee, check branches
  Case scrut x1 e1 x2 e2 -> do
    t <- infer ctx scrut
    case t of
      TySum a b -> do
        t1 <- infer (extendCtx x1 a ctx) e1
        t2 <- infer (extendCtx x2 b ctx) e2
        unless (typeEq t1 t2) $
          throwError $ TypeMismatch t1 t2
        return t1
      _ -> throwError $ ExpectedSum t

  -- Type application
  TyApp e ty -> do
    wfType ctx ty
    t <- infer ctx e
    case t of
      TyForall a body -> return $ substType a ty body
      _ -> throwError $ ExpectedForall t

  -- Terms that can only be checked, not inferred
  Lam _ _ -> throwError $ CannotInfer (Lam "_" (Var "_"))
  Pair _ _ -> throwError $ CannotInfer (Pair TmUnit TmUnit)
  Inl _ -> throwError $ CannotInfer (Inl TmUnit)
  Inr _ -> throwError $ CannotInfer (Inr TmUnit)
  TyLam _ _ -> throwError $ CannotInfer (TyLam "_" TmUnit)

-- ============================================================
-- CHECKING MODE (⇐)
-- ============================================================

-- | Check a term against a type
--
-- Γ ⊢ e ⇐ A
--
-- Succeeds if e has type A, fails otherwise.
check :: Ctx -> Term -> Type -> TC ()
check ctx term ty = case (term, ty) of
  -- Lambda introduction
  -- Γ, x:A ⊢ e ⇐ B
  -- ─────────────────────
  -- Γ ⊢ λx. e ⇐ A → B
  (Lam x body, TyArr a b) -> do
    check (extendCtx x a ctx) body b

  -- Annotated lambda: still works in checking mode
  (LamAnn x a body, TyArr a' b) -> do
    unless (typeEq a a') $
      throwError $ TypeMismatch a a'
    check (extendCtx x a ctx) body b

  -- Pair introduction
  -- Γ ⊢ e1 ⇐ A    Γ ⊢ e2 ⇐ B
  -- ──────────────────────────
  -- Γ ⊢ (e1, e2) ⇐ A × B
  (Pair e1 e2, TyProd a b) -> do
    check ctx e1 a
    check ctx e2 b

  -- Sum introductions
  -- Γ ⊢ e ⇐ A
  -- ─────────────────────
  -- Γ ⊢ inl e ⇐ A + B
  (Inl e, TySum a _) -> check ctx e a
  (Inr e, TySum _ b) -> check ctx e b

  -- Type abstraction
  -- Γ, α ⊢ e ⇐ A
  -- ─────────────────────
  -- Γ ⊢ Λα. e ⇐ ∀α. A
  (TyLam a body, TyForall a' bodyTy) -> do
    -- Rename if necessary (for simplicity, assume names match)
    when (a /= a') $
      throwError $ TypeMismatch (TyForall a TyUnit) (TyForall a' bodyTy)
    check (extendTyCtx a ctx) body bodyTy

  -- Subsumption: fall back to inference
  -- Γ ⊢ e ⇒ A    A = B
  -- ────────────────────
  -- Γ ⊢ e ⇐ B
  (e, expected) -> do
    inferred <- infer ctx e
    unless (typeEq inferred expected) $
      throwError $ TypeMismatch expected inferred
