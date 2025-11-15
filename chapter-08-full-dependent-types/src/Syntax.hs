{-# LANGUAGE LambdaCase #-}

module Syntax
  ( Name, Level
  , Term(..), Pattern(..)
  , InductiveDef(..), Constructor(..)
  , freeVars
  , patternVars
  , subst
  , freshName
  , alphaEq
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

type Name = String
type Level = Int

-- | Inductive type definition
data InductiveDef = InductiveDef
  { indName :: Name           -- Name of the type
  , indParams :: [(Name, Term)]  -- Parameters (e.g., A in Vec A n)
  , indIndices :: [(Name, Term)] -- Indices (e.g., n in Vec A n)
  , indType :: Term           -- Type of the inductive type
  , indConstructors :: [Constructor]
  } deriving (Eq, Show)

-- | Constructor of an inductive type
data Constructor = Constructor
  { conName :: Name
  , conType :: Term           -- Type of the constructor
  } deriving (Eq, Show)

-- | Patterns for pattern matching
data Pattern
  = PVar Name                 -- Variable pattern
  | PCon Name [Pattern]       -- Constructor pattern
  | PWild                     -- Wildcard _
  deriving (Eq, Show, Ord)

-- | Terms in full dependent type theory
data Term
  -- Universe hierarchy
  = Universe Level            -- Type i (where i is the level)

  -- Variables and binding
  | Var Name
  | Lam Name Term Term        -- λ(x:A). t
  | App Term Term             -- t₁ t₂

  -- Dependent types
  | Pi Name Term Term         -- Π(x:A). B
  | Sigma Name Term Term      -- Σ(x:A). B
  | Pair Term Term            -- (t₁, t₂)
  | Fst Term                  -- fst t
  | Snd Term                  -- snd t

  -- Inductive types
  | Ind Name                  -- Reference to inductive type
  | Con Name [Term]           -- Constructor application
  | Match Term [(Pattern, Term)] -- Pattern matching

  -- Equality type (propositional equality)
  | Eq Term Term Term         -- Eq A x y  (x = y in type A)
  | Refl Term                 -- refl x    (proof that x = x)
  | J Term Term Term Term Term Term
    -- J(A, C, p, x, y, eq)
    -- Elimination principle for equality
    -- If eq : x = y, C : (z:A) → x = z → Type, p : C x (refl x)
    -- then J produces C y eq

  -- Natural numbers (built-in for convenience)
  | Nat
  | Zero
  | Succ Term
  | NatElim Term Term Term Term
    -- natElim(P, z, s, n)
    -- P : Nat → Type, z : P 0, s : Π(k:Nat). P k → P (succ k), n : Nat

  -- Booleans
  | Bool
  | TmTrue
  | TmFalse
  | BoolElim Term Term Term Term
    -- boolElim(P, t, f, b)
    -- P : Bool → Type, t : P true, f : P false, b : Bool

  -- Unit and Empty types
  | Unit
  | TT                        -- () : Unit
  | UnitElim Term Term Term
    -- unitElim(P, u, x)
    -- P : Unit → Type, u : P (), x : Unit

  | Empty                     -- ⊥ (empty type, no constructors)
  | EmptyElim Term Term
    -- emptyElim(P, e)
    -- P : Empty → Type, e : Empty
    -- Can eliminate to any type (ex falso quodlibet)

  deriving (Eq, Show, Ord)

-- | Free variables in a term
freeVars :: Term -> Set Name
freeVars = \case
  Universe _ -> Set.empty
  Var x -> Set.singleton x
  Lam x ty t -> Set.delete x (freeVars ty `Set.union` freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Pi x a b -> Set.delete x (freeVars a `Set.union` freeVars b)
  Sigma x a b -> Set.delete x (freeVars a `Set.union` freeVars b)
  Pair t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Fst t -> freeVars t
  Snd t -> freeVars t
  Ind _ -> Set.empty
  Con _ ts -> Set.unions (map freeVars ts)
  Match t branches -> freeVars t `Set.union`
    Set.unions [freeVars rhs Set.\\ patternVars pat | (pat, rhs) <- branches]
  Eq a x y -> freeVars a `Set.union` freeVars x `Set.union` freeVars y
  Refl t -> freeVars t
  J a c p x y eq -> Set.unions [freeVars a, freeVars c, freeVars p, freeVars x, freeVars y, freeVars eq]
  Nat -> Set.empty
  Zero -> Set.empty
  Succ t -> freeVars t
  NatElim p z s n -> Set.unions [freeVars p, freeVars z, freeVars s, freeVars n]
  Bool -> Set.empty
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  BoolElim p t f b -> Set.unions [freeVars p, freeVars t, freeVars f, freeVars b]
  Unit -> Set.empty
  TT -> Set.empty
  UnitElim p u x -> Set.unions [freeVars p, freeVars u, freeVars x]
  Empty -> Set.empty
  EmptyElim p e -> freeVars p `Set.union` freeVars e

-- | Variables in a pattern
patternVars :: Pattern -> Set Name
patternVars = \case
  PVar x -> Set.singleton x
  PCon _ ps -> Set.unions (map patternVars ps)
  PWild -> Set.empty

-- | Substitution: [x ↦ s]t
subst :: Name -> Term -> Term -> Term
subst x s = \case
  Universe l -> Universe l
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
  Ind name -> Ind name
  Con name ts -> Con name (map (subst x s) ts)
  Match t branches -> Match (subst x s t) [(pat, substBranch pat rhs) | (pat, rhs) <- branches]
    where
      substBranch pat rhs
        | x `Set.member` patternVars pat = rhs
        | otherwise = subst x s rhs
  Eq a t1 t2 -> Eq (subst x s a) (subst x s t1) (subst x s t2)
  Refl t -> Refl (subst x s t)
  J a c p x1 y eq -> J (subst x s a) (subst x s c) (subst x s p) (subst x s x1) (subst x s y) (subst x s eq)
  Nat -> Nat
  Zero -> Zero
  Succ t -> Succ (subst x s t)
  NatElim p z step n -> NatElim (subst x s p) (subst x s z) (subst x s step) (subst x s n)
  Bool -> Bool
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  BoolElim p t f b -> BoolElim (subst x s p) (subst x s t) (subst x s f) (subst x s b)
  Unit -> Unit
  TT -> TT
  UnitElim p u val -> UnitElim (subst x s p) (subst x s u) (subst x s val)
  Empty -> Empty
  EmptyElim p e -> EmptyElim (subst x s p) (subst x s e)

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
      (Universe l1, Universe l2) -> l1 == l2
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
      (Ind n1, Ind n2) -> n1 == n2
      (Con n1 ts1, Con n2 ts2) -> n1 == n2 && length ts1 == length ts2 &&
        all (uncurry (go bound1 bound2)) (zip ts1 ts2)
      (Eq a1 x1 y1, Eq a2 x2 y2) ->
        go bound1 bound2 a1 a2 && go bound1 bound2 x1 x2 && go bound1 bound2 y1 y2
      (Refl a, Refl b) -> go bound1 bound2 a b
      (Nat, Nat) -> True
      (Zero, Zero) -> True
      (Succ a, Succ b) -> go bound1 bound2 a b
      (Bool, Bool) -> True
      (TmTrue, TmTrue) -> True
      (TmFalse, TmFalse) -> True
      (Unit, Unit) -> True
      (TT, TT) -> True
      (Empty, Empty) -> True
      _ -> False
