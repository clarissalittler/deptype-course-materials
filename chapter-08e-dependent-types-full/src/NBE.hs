{-# LANGUAGE LambdaCase #-}

module NBE
  ( normalize
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)

-- | Semantic values
data Value
  = VUniverse Level
  | VLam Name Value Term Env
  | VPi Name Value Term Env
  | VSigma Name Value Term Env
  | VPair Value Value
  | VNeutral Neutral
  | VNat
  | VZero
  | VSucc Value
  | VBool
  | VTrue
  | VFalse
  | VUnit
  | VTT
  | VEmpty
  | VEq Value Value Value
  | VRefl Value
  | VInd Name
  | VCon Name [Value]

data Neutral
  = NVar Name
  | NInd Name
  | NApp Neutral Value
  | NFst Neutral
  | NSnd Neutral
  | NNatElim Value Value Value Neutral
  | NBoolElim Value Value Value Neutral
  | NUnitElim Value Value Neutral
  | NEmptyElim Value Neutral
  | NJ Value Value Value Value Value Neutral
  | NMatch Value (Maybe Value) [(Pattern, Term)]

type Env = Map Name Value

-- | Normalize a term via NBE
normalize :: Term -> Term
normalize t = quote Set.empty (eval Map.empty t)

-- | Evaluate a term to a semantic value
eval :: Env -> Term -> Value
eval env = \case
  Universe l -> VUniverse l
  Var x -> Map.findWithDefault (VNeutral (NVar x)) x env
  Lam x ty t -> VLam x (eval env ty) t env
  App t1 t2 -> vApp (eval env t1) (eval env t2)
  Pi x a b -> VPi x (eval env a) b env
  Sigma x a b -> VSigma x (eval env a) b env
  Pair t1 t2 -> VPair (eval env t1) (eval env t2)
  Fst t -> vFst (eval env t)
  Snd t -> vSnd (eval env t)
  Ind name -> VInd name
  Con name ts -> VCon name (map (eval env) ts)
  Match t motive branches -> VNeutral (NMatch (eval env t) (fmap (eval env) motive) branches)
  Eq a x y -> VEq (eval env a) (eval env x) (eval env y)
  Refl t -> VRefl (eval env t)
  J a c p x y eq ->
    let a' = eval env a
        c' = eval env c
        p' = eval env p
        x' = eval env x
        y' = eval env y
        eq' = eval env eq
    in vJ a' c' p' x' y' eq'
  Nat -> VNat
  Zero -> VZero
  Succ t -> VSucc (eval env t)
  NatElim p z s n -> vNatElim (eval env p) (eval env z) (eval env s) (eval env n)
  Bool -> VBool
  TmTrue -> VTrue
  TmFalse -> VFalse
  BoolElim p t f b -> vBoolElim (eval env p) (eval env t) (eval env f) (eval env b)
  Unit -> VUnit
  TT -> VTT
  UnitElim p u x -> vUnitElim (eval env p) (eval env u) (eval env x)
  Empty -> VEmpty
  EmptyElim p e -> vEmptyElim (eval env p) (eval env e)

vApp :: Value -> Value -> Value
vApp (VLam x _ body env) v = eval (Map.insert x v env) body
vApp (VNeutral n) v = VNeutral (NApp n v)
vApp (VInd name) v = VNeutral (NApp (NInd name) v)
vApp _ v = VNeutral (NApp (NVar "<app>") v)

vFst :: Value -> Value
vFst (VPair v1 _) = v1
vFst (VNeutral n) = VNeutral (NFst n)
vFst _ = VNeutral (NFst (NVar "<fst>"))

vSnd :: Value -> Value
vSnd (VPair _ v2) = v2
vSnd (VNeutral n) = VNeutral (NSnd n)
vSnd _ = VNeutral (NSnd (NVar "<snd>"))

vNatElim :: Value -> Value -> Value -> Value -> Value
vNatElim p z s n = case n of
  VZero -> z
  VSucc k -> vApp (vApp s k) (vNatElim p z s k)
  VNeutral n' -> VNeutral (NNatElim p z s n')
  _ -> VNeutral (NNatElim p z s (NVar "<nat>"))

vBoolElim :: Value -> Value -> Value -> Value -> Value
vBoolElim p t f b = case b of
  VTrue -> t
  VFalse -> f
  VNeutral n -> VNeutral (NBoolElim p t f n)
  _ -> VNeutral (NBoolElim p t f (NVar "<bool>"))

vUnitElim :: Value -> Value -> Value -> Value
vUnitElim p u x = case x of
  VTT -> u
  VNeutral n -> VNeutral (NUnitElim p u n)
  _ -> VNeutral (NUnitElim p u (NVar "<unit>"))

vEmptyElim :: Value -> Value -> Value
vEmptyElim p e = case e of
  VNeutral n -> VNeutral (NEmptyElim p n)
  _ -> VNeutral (NEmptyElim p (NVar "<empty>"))

vJ :: Value -> Value -> Value -> Value -> Value -> Value -> Value
vJ a c p x y eq = case eq of
  VRefl _ -> p
  VNeutral n -> VNeutral (NJ a c p x y n)
  _ -> VNeutral (NJ a c p x y (NVar "<eq>"))

-- | Quote a semantic value back to a term
quote :: Set Name -> Value -> Term
quote used = \case
  VUniverse l -> Universe l
  VLam x ty body env ->
    let x' = freshName x used
        vX = VNeutral (NVar x')
        bodyVal = eval (Map.insert x vX env) body
        used' = Set.insert x' used
    in Lam x' (quote used ty) (quote used' bodyVal)
  VPi x a body env ->
    let x' = freshName x used
        vX = VNeutral (NVar x')
        bodyVal = eval (Map.insert x vX env) body
        used' = Set.insert x' used
    in Pi x' (quote used a) (quote used' bodyVal)
  VSigma x a body env ->
    let x' = freshName x used
        vX = VNeutral (NVar x')
        bodyVal = eval (Map.insert x vX env) body
        used' = Set.insert x' used
    in Sigma x' (quote used a) (quote used' bodyVal)
  VPair v1 v2 -> Pair (quote used v1) (quote used v2)
  VNeutral n -> quoteNeutral used n
  VNat -> Nat
  VZero -> Zero
  VSucc v -> Succ (quote used v)
  VBool -> Bool
  VTrue -> TmTrue
  VFalse -> TmFalse
  VUnit -> Unit
  VTT -> TT
  VEmpty -> Empty
  VEq a x y -> Eq (quote used a) (quote used x) (quote used y)
  VRefl v -> Refl (quote used v)
  VInd name -> Ind name
  VCon name vs -> Con name (map (quote used) vs)

quoteNeutral :: Set Name -> Neutral -> Term
quoteNeutral used = \case
  NVar x -> Var x
  NInd name -> Ind name
  NApp n v -> App (quoteNeutral used n) (quote used v)
  NFst n -> Fst (quoteNeutral used n)
  NSnd n -> Snd (quoteNeutral used n)
  NNatElim p z s n -> NatElim (quote used p) (quote used z) (quote used s) (quoteNeutral used n)
  NBoolElim p t f n -> BoolElim (quote used p) (quote used t) (quote used f) (quoteNeutral used n)
  NUnitElim p u n -> UnitElim (quote used p) (quote used u) (quoteNeutral used n)
  NEmptyElim p n -> EmptyElim (quote used p) (quoteNeutral used n)
  NJ a c p x y n -> J (quote used a) (quote used c) (quote used p) (quote used x) (quote used y) (quoteNeutral used n)
  NMatch v motive branches -> Match (quote used v) (fmap (quote used) motive) branches
