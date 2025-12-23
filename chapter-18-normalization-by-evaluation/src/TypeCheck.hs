{-# LANGUAGE LambdaCase #-}
-- | Type Checking with NbE
--
-- This module demonstrates how NbE enables type checking for dependent types.
-- The key insight: to check if two types are equal, normalize them and compare.

module TypeCheck
  ( -- * Type Checking
    check
  , infer
  , TypeError(..)
    -- * Context
  , Ctx
  , emptyCtx
  ) where

import Control.Monad (unless)
import Control.Monad.Except
import qualified Data.Map.Strict as Map

import Syntax
import Semantic
import NbE

-- | Type errors
data TypeError
  = UnboundVariable Name
  | TypeMismatch Nf Nf
  | ExpectedPi Nf
  | ExpectedBool Nf
  | ExpectedNat Nf
  | NotAType Nf
  deriving (Eq, Show)

-- | Typing context
--
-- We track both types (for type checking) and values (for NbE).
data Ctx = Ctx
  { ctxTypes :: [Val]         -- ^ Types of variables (innermost first)
  , ctxEnv   :: Env           -- ^ Values for evaluation
  , ctxLvl   :: Lvl           -- ^ Current de Bruijn level
  , ctxNames :: [Name]        -- ^ Names for error messages
  }

emptyCtx :: Ctx
emptyCtx = Ctx [] [] 0 []

-- | Extend context with a new binding
extendCtx :: Name -> Val -> Val -> Ctx -> Ctx
extendCtx name ty val ctx = Ctx
  { ctxTypes = ty : ctxTypes ctx
  , ctxEnv = val : ctxEnv ctx
  , ctxLvl = ctxLvl ctx + 1
  , ctxNames = name : ctxNames ctx
  }

-- | Extend context with just a type (for Pi introduction)
extendCtxType :: Name -> Val -> Ctx -> Ctx
extendCtxType name ty ctx =
  let var = VNe (NVar (ctxLvl ctx))
  in extendCtx name ty var ctx

-- | Type checking monad
type TC = Either TypeError

-- | Check that two values are equal (by normalization)
conversionCheck :: Ctx -> Val -> Val -> TC ()
conversionCheck ctx v1 v2 = do
  let nf1 = quote (ctxLvl ctx) v1
      nf2 = quote (ctxLvl ctx) v2
  unless (nf1 == nf2) $
    throwError $ TypeMismatch nf1 nf2

-- | Check that a value is a type
checkType :: Ctx -> Val -> TC ()
checkType ctx v = case v of
  VU -> return ()
  VBool -> return ()
  VNat -> return ()
  VPi _ a b -> do
    checkType ctx a
    let ctx' = extendCtxType "_" a ctx
        bVal = applyClosure b (VNe (NVar (ctxLvl ctx)))
    checkType ctx' bVal
  VNe _ -> return ()  -- Neutral types are ok (might become types)
  _ -> throwError $ NotAType (quote (ctxLvl ctx) v)

-- | Infer the type of a term
infer :: Ctx -> Term -> TC Val
infer ctx = \case
  TVar i ->
    if i < length (ctxTypes ctx)
      then return $ ctxTypes ctx !! i
      else throwError $ UnboundVariable (show i)

  TLam x t -> do
    -- We need a type annotation for lambdas
    -- For now, fail (bidirectional typing would help here)
    throwError $ UnboundVariable "Cannot infer lambda type"

  TApp t u -> do
    tTy <- infer ctx t
    case tTy of
      VPi _ a b -> do
        check ctx u a
        let uVal = eval (ctxEnv ctx) u
        return $ applyClosure b uVal
      _ -> throwError $ ExpectedPi (quote (ctxLvl ctx) tTy)

  TPi x a b -> do
    check ctx a VU
    let aVal = eval (ctxEnv ctx) a
        ctx' = extendCtxType x aVal ctx
    check ctx' b VU
    return VU

  TU -> return VU  -- Type : Type (simplified, inconsistent)

  TLet x a t u -> do
    check ctx a VU
    let aVal = eval (ctxEnv ctx) a
    check ctx t aVal
    let tVal = eval (ctxEnv ctx) t
        ctx' = extendCtx x aVal tVal ctx
    infer ctx' u

  TBool -> return VU
  TTrue -> return VBool
  TFalse -> return VBool

  TIf b t f -> do
    check ctx b VBool
    tTy <- infer ctx t
    fTy <- infer ctx f
    conversionCheck ctx tTy fTy
    return tTy

  TNat -> return VU
  TZero -> return VNat
  TSuc n -> do
    check ctx n VNat
    return VNat

  TNatElim p z s n -> do
    -- P : Nat -> U
    check ctx p (VPi "_" VNat (Closure [] TU))
    let pVal = eval (ctxEnv ctx) p

    -- z : P 0
    check ctx z (vApp pVal VZero)

    -- s : (m : Nat) -> P m -> P (suc m)
    let sTy = VPi "m" VNat $ Closure (ctxEnv ctx) $
                TPi "_" (TApp (TVar 1) (TVar 0))  -- P m
                        (TApp (TVar 2) (TSuc (TVar 1)))  -- P (suc m)
    check ctx s sTy

    check ctx n VNat
    let nVal = eval (ctxEnv ctx) n
    return $ vApp pVal nVal

-- | Check a term against a type
check :: Ctx -> Term -> Val -> TC ()
check ctx t ty = case (t, ty) of
  -- Lambda introduction
  (TLam x body, VPi _ a b) -> do
    let ctx' = extendCtxType x a ctx
        bVal = applyClosure b (VNe (NVar (ctxLvl ctx)))
    check ctx' body bVal

  -- Fall back to inference
  _ -> do
    ty' <- infer ctx t
    conversionCheck ctx ty ty'
