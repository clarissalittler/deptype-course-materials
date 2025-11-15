{-# LANGUAGE LambdaCase #-}

module Syntax
  ( Name
  , Term(..)
  , freeVars
  , subst
  , freshName
  , alphaEq
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

type Name = String

-- | In dependent type theory, terms and types are unified
-- since types can depend on terms
data Term
  -- Type universe
  = Type                       -- ^ The type of types (universe)

  -- Variables and binding
  | Var Name                   -- ^ Variable
  | Lam Name Term Term         -- ^ Lambda λ(x:A). t
  | App Term Term              -- ^ Application t₁ t₂

  -- Dependent function types (Pi types)
  | Pi Name Term Term          -- ^ Π(x:A). B  (dependent function type)

  -- Dependent pair types (Sigma types)
  | Sigma Name Term Term       -- ^ Σ(x:A). B  (dependent pair type)
  | Pair Term Term             -- ^ (t₁, t₂)   (pair introduction)
  | Fst Term                   -- ^ fst t     (first projection)
  | Snd Term                   -- ^ snd t     (second projection)

  -- Natural numbers (for examples)
  | Nat                        -- ^ Nat type
  | Zero                       -- ^ 0
  | Succ Term                  -- ^ succ n

  -- Booleans (for examples)
  | Bool                       -- ^ Bool type
  | TmTrue                     -- ^ true
  | TmFalse                    -- ^ false
  | If Term Term Term          -- ^ if t then t else t

  deriving (Eq, Show, Ord)

-- | Free variables in a term
freeVars :: Term -> Set Name
freeVars = \case
  Type -> Set.empty
  Var x -> Set.singleton x
  Lam x ty t -> Set.delete x (freeVars ty `Set.union` freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Pi x a b -> Set.delete x (freeVars a `Set.union` freeVars b)
  Sigma x a b -> Set.delete x (freeVars a `Set.union` freeVars b)
  Pair t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Fst t -> freeVars t
  Snd t -> freeVars t
  Nat -> Set.empty
  Zero -> Set.empty
  Succ t -> freeVars t
  Bool -> Set.empty
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  If t1 t2 t3 -> freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3

-- | Substitution: [x ↦ s]t
subst :: Name -> Term -> Term -> Term
subst x s = \case
  Type -> Type
  Var y | y == x -> s
        | otherwise -> Var y
  Lam y ty t
    | y == x -> Lam y (subst x s ty) t
    | y `Set.member` fvs ->
        let y' = freshName y (fvs `Set.union` freeVars t `Set.union` freeVars ty)
            t' = subst y (Var y') t
            ty' = subst y (Var y') ty
        in Lam y' (subst x s ty') (subst x s t')
    | otherwise -> Lam y (subst x s ty) (subst x s t)
    where fvs = freeVars s
  App t1 t2 -> App (subst x s t1) (subst x s t2)
  Pi y a b
    | y == x -> Pi y (subst x s a) b
    | y `Set.member` fvs ->
        let y' = freshName y (fvs `Set.union` freeVars a `Set.union` freeVars b)
            a' = subst y (Var y') a
            b' = subst y (Var y') b
        in Pi y' (subst x s a') (subst x s b')
    | otherwise -> Pi y (subst x s a) (subst x s b)
    where fvs = freeVars s
  Sigma y a b
    | y == x -> Sigma y (subst x s a) b
    | y `Set.member` fvs ->
        let y' = freshName y (fvs `Set.union` freeVars a `Set.union` freeVars b)
            a' = subst y (Var y') a
            b' = subst y (Var y') b
        in Sigma y' (subst x s a') (subst x s b')
    | otherwise -> Sigma y (subst x s a) (subst x s b)
    where fvs = freeVars s
  Pair t1 t2 -> Pair (subst x s t1) (subst x s t2)
  Fst t -> Fst (subst x s t)
  Snd t -> Snd (subst x s t)
  Nat -> Nat
  Zero -> Zero
  Succ t -> Succ (subst x s t)
  Bool -> Bool
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  If t1 t2 t3 -> If (subst x s t1) (subst x s t2) (subst x s t3)

-- | Generate a fresh name
freshName :: Name -> Set Name -> Name
freshName base used = head $ filter (`Set.notMember` used) candidates
  where candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]

-- | Alpha equivalence (structural equality up to variable renaming)
alphaEq :: Term -> Term -> Bool
alphaEq = go Set.empty Set.empty
  where
    go :: Set (Name, Name) -> Set (Name, Name) -> Term -> Term -> Bool
    go bound1 bound2 t1 t2 = case (t1, t2) of
      (Type, Type) -> True
      (Var x, Var y) -> x == y || Set.member (x, y) bound1 || Set.member (y, x) bound2
      (Lam x ty1 t1', Lam y ty2 t2') ->
        go bound1 bound2 ty1 ty2 &&
        go (Set.insert (x, y) bound1) (Set.insert (y, x) bound2) t1' t2'
      (App a1 a2, App b1 b2) -> go bound1 bound2 a1 b1 && go bound1 bound2 a2 b2
      (Pi x a1 b1, Pi y a2 b2) ->
        go bound1 bound2 a1 a2 &&
        go (Set.insert (x, y) bound1) (Set.insert (y, x) bound2) b1 b2
      (Sigma x a1 b1, Sigma y a2 b2) ->
        go bound1 bound2 a1 a2 &&
        go (Set.insert (x, y) bound1) (Set.insert (y, x) bound2) b1 b2
      (Pair a1 a2, Pair b1 b2) -> go bound1 bound2 a1 b1 && go bound1 bound2 a2 b2
      (Fst a, Fst b) -> go bound1 bound2 a b
      (Snd a, Snd b) -> go bound1 bound2 a b
      (Nat, Nat) -> True
      (Zero, Zero) -> True
      (Succ a, Succ b) -> go bound1 bound2 a b
      (Bool, Bool) -> True
      (TmTrue, TmTrue) -> True
      (TmFalse, TmFalse) -> True
      (If a1 a2 a3, If b1 b2 b3) ->
        go bound1 bound2 a1 b1 && go bound1 bound2 a2 b2 && go bound1 bound2 a3 b3
      _ -> False
