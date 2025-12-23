{-# LANGUAGE LambdaCase #-}
-- | Evaluator for bidirectional terms

module Eval
  ( eval
  , evalClosed
  ) where

import Syntax
import qualified Data.Map.Strict as Map

-- | Evaluate a term to a value
eval :: Env -> Term -> Val
eval env = \case
  Var x ->
    case Map.lookup x env of
      Just v  -> v
      Nothing -> VNeutral (NVar x)

  Lam x body ->
    VLam x (Closure env body)

  LamAnn x _ body ->
    VLam x (Closure env body)

  App e1 e2 ->
    let v1 = eval env e1
        v2 = eval env e2
    in vApp v1 v2

  Ann e _ -> eval env e

  Let x e1 e2 ->
    let v1 = eval env e1
    in eval (extendEnv x v1 env) e2

  TmTrue -> VBool True
  TmFalse -> VBool False

  If cond thn els ->
    case eval env cond of
      VBool True  -> eval env thn
      VBool False -> eval env els
      VNeutral n  -> VNeutral (NIf n (eval env thn) (eval env els))
      _ -> error "If: non-boolean condition"

  Zero -> VNat 0
  Suc n ->
    case eval env n of
      VNat m -> VNat (m + 1)
      v -> error $ "Suc: non-nat " ++ show v

  NatRec z s n ->
    let vz = eval env z
        vs = eval env s
    in natRec vz vs (eval env n)

  TmUnit -> VUnit

  Pair e1 e2 -> VPair (eval env e1) (eval env e2)

  Fst e ->
    case eval env e of
      VPair v1 _ -> v1
      VNeutral n -> VNeutral (NFst n)
      v -> error $ "Fst: non-pair " ++ show v

  Snd e ->
    case eval env e of
      VPair _ v2 -> v2
      VNeutral n -> VNeutral (NSnd n)
      v -> error $ "Snd: non-pair " ++ show v

  Inl e -> VInl (eval env e)
  Inr e -> VInr (eval env e)

  Case scrut x1 e1 x2 e2 ->
    case eval env scrut of
      VInl v -> eval (extendEnv x1 v env) e1
      VInr v -> eval (extendEnv x2 v env) e2
      VNeutral n ->
        let v1 = VLam x1 (Closure env e1)
            v2 = VLam x2 (Closure env e2)
        in VNeutral (NCase n x1 (eval env e1) x2 (eval env e2))
      v -> error $ "Case: non-sum " ++ show v

  TyLam a body ->
    VTyLam a (Closure env body)

  TyApp e _ ->
    case eval env e of
      VTyLam _ (Closure env' body) -> eval env' body
      VNeutral n -> VNeutral (NTyApp n undefined)
      v -> error $ "TyApp: non-forall " ++ show v

-- | Apply a value to an argument
vApp :: Val -> Val -> Val
vApp (VLam x (Closure env body)) arg =
  eval (extendEnv x arg env) body
vApp (VNeutral n) arg =
  VNeutral (NApp n arg)
vApp v _ = error $ "vApp: non-function " ++ show v

-- | Natural number recursion
natRec :: Val -> Val -> Val -> Val
natRec z _ (VNat 0) = z
natRec z s (VNat n) =
  let prev = natRec z s (VNat (n - 1))
  in vApp (vApp s (VNat (n - 1))) prev
natRec z s (VNeutral n) =
  VNeutral (NNatRec z s n)
natRec _ _ v = error $ "natRec: non-nat " ++ show v

-- | Evaluate a closed term
evalClosed :: Term -> Val
evalClosed = eval emptyEnv
