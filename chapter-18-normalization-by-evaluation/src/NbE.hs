{-# LANGUAGE LambdaCase #-}
-- | Normalization by Evaluation
--
-- NbE works in two phases:
--
-- 1. EVALUATION: Term → Val
--    Evaluate syntactic terms into semantic values.
--    Uses the host language (Haskell) to do beta reduction.
--
-- 2. QUOTATION: Val → Nf
--    "Read back" semantic values into normal forms.
--    This is where we generate fresh variables for lambdas.
--
-- The composition gives us: normalize = quote ∘ eval
--
-- Why is this useful?
-- - Type checking dependent types requires comparing types for equality
-- - Types can contain arbitrary terms, so we need normalization
-- - NbE is efficient and elegant

module NbE
  ( -- * Core Operations
    eval
  , quote
  , normalize
    -- * Application
  , vApp
  , vIf
  , vNatElim
    -- * Closure Operations
  , applyClosure
  ) where

import Syntax
import Semantic

-- | Evaluate a term to a semantic value
--
-- This is where the magic happens: we use Haskell's own evaluation
-- to implement beta reduction!
eval :: Env -> Term -> Val
eval env = \case
  TVar i ->
    case lookupEnv i env of
      Just v  -> v
      Nothing -> error $ "Unbound variable: " ++ show i

  TLam x t ->
    VLam x (Closure env t)

  TApp t u ->
    vApp (eval env t) (eval env u)

  TPi x a b ->
    VPi x (eval env a) (Closure env b)

  TU -> VU

  TLet _ _ t u ->
    let v = eval env t
    in eval (extendEnv v env) u

  TBool -> VBool
  TTrue -> VTrue
  TFalse -> VFalse

  TIf b t f ->
    vIf (eval env b) (eval env t) (eval env f)

  TNat -> VNat
  TZero -> VZero
  TSuc n -> VSuc (eval env n)

  TNatElim p z s n ->
    vNatElim (eval env p) (eval env z) (eval env s) (eval env n)

-- | Apply a closure to a value
--
-- This is beta reduction!
-- closure = (λx. body, env)
-- applyClosure closure v = body[x := v]
applyClosure :: Closure -> Val -> Val
applyClosure (Closure env t) v = eval (extendEnv v env) t

-- | Apply a semantic function to an argument
--
-- If the function is a lambda, apply it.
-- If it's neutral, extend the spine.
vApp :: Val -> Val -> Val
vApp (VLam _ closure) arg = applyClosure closure arg
vApp (VNe neutral) arg = VNe (NApp neutral arg)
vApp _ _ = error "vApp: not a function"

-- | Evaluate if-then-else
vIf :: Val -> Val -> Val -> Val
vIf VTrue  t _ = t
vIf VFalse _ f = f
vIf (VNe n) t f = VNe (NIf n t f)
vIf _ _ _ = error "vIf: not a boolean"

-- | Evaluate natural number eliminator
--
-- natElim P z s n computes:
--   natElim P z s zero    = z
--   natElim P z s (suc m) = s m (natElim P z s m)
vNatElim :: Val -> Val -> Val -> Val -> Val
vNatElim _ z _ VZero = z
vNatElim p z s (VSuc m) =
  let ih = vNatElim p z s m  -- induction hypothesis
  in vApp (vApp s m) ih
vNatElim p z s (VNe n) = VNe (NNatElim p z s n)
vNatElim _ _ _ _ = error "vNatElim: not a natural"

-- | Quote a semantic value back to a normal form
--
-- This is the "read back" phase.
-- We need the current de Bruijn level to generate fresh variables.
quote :: Lvl -> Val -> Nf
quote l = \case
  VLam x closure ->
    -- To quote a lambda, we need to:
    -- 1. Create a fresh variable at the current level
    -- 2. Apply the closure to this variable
    -- 3. Quote the result at level+1
    let var = VNe (NVar l)
        body = applyClosure closure var
    in NfLam x (quote (l + 1) body)

  VPi x a closure ->
    let var = VNe (NVar l)
        b = applyClosure closure var
    in NfPi x (quote l a) (quote (l + 1) b)

  VU -> NfU

  VNe neutral -> NfNe (quoteNe l neutral)

  VBool -> NfBool
  VTrue -> NfTrue
  VFalse -> NfFalse

  VNat -> NfNat
  VZero -> NfZero
  VSuc v -> NfSuc (quote l v)

-- | Quote a neutral value
quoteNe :: Lvl -> Neutral -> Ne
quoteNe l = \case
  NVar x ->
    -- Convert level to index
    NeVar x

  NApp n v ->
    NeApp (quoteNe l n) (quote l v)

  NIf n t f ->
    NeIf (quoteNe l n) (quote l t) (quote l f)

  NNatElim p z s n ->
    NeNatElim (quote l p) (quote l z) (quote l s) (quoteNe l n)

-- | Normalize a closed term
--
-- This is the main entry point.
-- normalize = quote ∘ eval
normalize :: Term -> Nf
normalize t = quote 0 (eval emptyEnv t)

-- | Normalize an open term with a given environment
normalizeOpen :: Env -> Lvl -> Term -> Nf
normalizeOpen env l t = quote l (eval env t)
