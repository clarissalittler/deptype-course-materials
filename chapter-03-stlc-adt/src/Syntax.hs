{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables and Labels
    Var
  , Label
    -- * Types
  , Type(..)
    -- * Patterns
  , Pattern(..)
    -- * Terms
  , Term(..)
    -- * Free variables
  , freeVars
    -- * Substitution
  , substVar
  , freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- | Variables
type Var = String

-- | Labels for records and variants
type Label = String

-- | Types in STLC with algebraic data types
data Type
  = TyVar Var                  -- ^ Type variable
  | TyArr Type Type            -- ^ Function type: τ₁ → τ₂
  | TyBool                     -- ^ Boolean type
  | TyNat                      -- ^ Natural number type
  | TyUnit                     -- ^ Unit type
  | TyProd Type Type           -- ^ Product type: τ₁ × τ₂
  | TySum Type Type            -- ^ Sum type: τ₁ + τ₂
  | TyRecord (Map Label Type)  -- ^ Record type: {l₁:τ₁, ..., lₙ:τₙ}
  | TyVariant (Map Label Type) -- ^ Variant type: <l₁:τ₁, ..., lₙ:τₙ>
  | TyList Type                -- ^ List type: List τ
  deriving (Eq, Show, Ord)

-- | Patterns for case expressions
data Pattern
  = PatVar Var                      -- ^ Variable pattern
  | PatWild                         -- ^ Wildcard pattern _
  | PatUnit                         -- ^ Unit pattern ()
  | PatTrue                         -- ^ Boolean pattern true
  | PatFalse                        -- ^ Boolean pattern false
  | PatZero                         -- ^ Zero pattern
  | PatSucc Pattern                 -- ^ Successor pattern (succ p)
  | PatPair Pattern Pattern         -- ^ Pair pattern (p₁, p₂)
  | PatInl Pattern                  -- ^ Left injection pattern (inl p)
  | PatInr Pattern                  -- ^ Right injection pattern (inr p)
  | PatVariant Label Pattern        -- ^ Variant pattern <l=p>
  | PatNil                          -- ^ Empty list pattern []
  | PatCons Pattern Pattern         -- ^ List cons pattern (p::ps)
  deriving (Eq, Show)

-- | Terms in STLC with ADTs
data Term
  = Var Var                         -- ^ Variable
  | Lam Var Type Term               -- ^ Lambda: λ(x:τ). t
  | App Term Term                   -- ^ Application: t₁ t₂

  -- Booleans
  | TmTrue                          -- ^ Boolean: true
  | TmFalse                         -- ^ Boolean: false
  | TmIf Term Term Term             -- ^ Conditional: if t₁ then t₂ else t₃

  -- Natural numbers
  | TmZero                          -- ^ Zero: 0
  | TmSucc Term                     -- ^ Successor: succ t
  | TmPred Term                     -- ^ Predecessor: pred t
  | TmIsZero Term                   -- ^ Zero test: iszero t

  -- Unit
  | TmUnit                          -- ^ Unit value: ()

  -- Products (pairs)
  | TmPair Term Term                -- ^ Pair: (t₁, t₂)
  | TmFst Term                      -- ^ First projection: fst t
  | TmSnd Term                      -- ^ Second projection: snd t

  -- Sums
  | TmInl Type Term                 -- ^ Left injection: inl[τ] t
  | TmInr Type Term                 -- ^ Right injection: inr[τ] t
  | TmCase Term Var Term Var Term   -- ^ Case: case t of inl x₁ => t₁ | inr x₂ => t₂

  -- Records
  | TmRecord (Map Label Term)       -- ^ Record: {l₁=t₁, ..., lₙ=tₙ}
  | TmProj Term Label               -- ^ Projection: t.l

  -- Variants
  | TmTag Label Term Type           -- ^ Variant: <l=t> as τ
  | TmCaseVariant Term [(Label, Var, Term)]  -- ^ Variant case

  -- Lists
  | TmNil Type                      -- ^ Empty list: [] : List τ
  | TmCons Term Term                -- ^ List cons: t::ts
  | TmIsNil Term                    -- ^ Nil test: isnil t
  | TmHead Term                     -- ^ List head: head t
  | TmTail Term                     -- ^ List tail: tail t

  -- Pattern matching
  | TmMatch Term [(Pattern, Term)]  -- ^ Pattern match: match t with p₁ => t₁ | ... | pₙ => tₙ

  deriving (Eq, Show)

-- | Compute free variables in a term
freeVars :: Term -> Set Var
freeVars = \case
  Var x -> Set.singleton x
  Lam x _ t -> Set.delete x (freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  TmIf t1 t2 t3 -> freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3
  TmZero -> Set.empty
  TmSucc t -> freeVars t
  TmPred t -> freeVars t
  TmIsZero t -> freeVars t
  TmUnit -> Set.empty
  TmPair t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmFst t -> freeVars t
  TmSnd t -> freeVars t
  TmInl _ t -> freeVars t
  TmInr _ t -> freeVars t
  TmCase t x1 t1 x2 t2 ->
    freeVars t `Set.union` Set.delete x1 (freeVars t1) `Set.union` Set.delete x2 (freeVars t2)
  TmRecord fields -> Set.unions (map freeVars (Map.elems fields))
  TmProj t _ -> freeVars t
  TmTag _ t _ -> freeVars t
  TmCaseVariant t cases ->
    freeVars t `Set.union` Set.unions [Set.delete x (freeVars ti) | (_, x, ti) <- cases]
  TmNil _ -> Set.empty
  TmCons t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmIsNil t -> freeVars t
  TmHead t -> freeVars t
  TmTail t -> freeVars t
  TmMatch t cases ->
    freeVars t `Set.union` Set.unions [freeVars ti Set.\\ patternVars pi | (pi, ti) <- cases]

-- | Get variables bound by a pattern
patternVars :: Pattern -> Set Var
patternVars = \case
  PatVar x -> Set.singleton x
  PatWild -> Set.empty
  PatUnit -> Set.empty
  PatTrue -> Set.empty
  PatFalse -> Set.empty
  PatZero -> Set.empty
  PatSucc p -> patternVars p
  PatPair p1 p2 -> patternVars p1 `Set.union` patternVars p2
  PatInl p -> patternVars p
  PatInr p -> patternVars p
  PatVariant _ p -> patternVars p
  PatNil -> Set.empty
  PatCons p ps -> patternVars p `Set.union` patternVars ps

-- | Capture-avoiding substitution
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y
    | y == x -> s
    | otherwise -> Var y
  Lam y ty t
    | y == x -> Lam y ty t
    | y `Set.member` fvs ->
        let y' = freshVar y (fvs `Set.union` freeVars t)
            t' = substVar y (Var y') t
        in Lam y' ty (substVar x s t')
    | otherwise -> Lam y ty (substVar x s t)
    where fvs = freeVars s
  App t1 t2 -> App (substVar x s t1) (substVar x s t2)
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 -> TmIf (substVar x s t1) (substVar x s t2) (substVar x s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substVar x s t)
  TmPred t -> TmPred (substVar x s t)
  TmIsZero t -> TmIsZero (substVar x s t)
  TmUnit -> TmUnit
  TmPair t1 t2 -> TmPair (substVar x s t1) (substVar x s t2)
  TmFst t -> TmFst (substVar x s t)
  TmSnd t -> TmSnd (substVar x s t)
  TmInl ty t -> TmInl ty (substVar x s t)
  TmInr ty t -> TmInr ty (substVar x s t)
  TmCase t y1 t1 y2 t2 ->
    let t' = substVar x s t
        t1' = if y1 == x then t1 else substVar x s t1
        t2' = if y2 == x then t2 else substVar x s t2
    in TmCase t' y1 t1' y2 t2'
  TmRecord fields -> TmRecord (Map.map (substVar x s) fields)
  TmProj t l -> TmProj (substVar x s t) l
  TmTag l t ty -> TmTag l (substVar x s t) ty
  TmCaseVariant t cases ->
    TmCaseVariant (substVar x s t)
      [(l, y, if y == x then ti else substVar x s ti) | (l, y, ti) <- cases]
  TmNil ty -> TmNil ty
  TmCons t1 t2 -> TmCons (substVar x s t1) (substVar x s t2)
  TmIsNil t -> TmIsNil (substVar x s t)
  TmHead t -> TmHead (substVar x s t)
  TmTail t -> TmTail (substVar x s t)
  TmMatch t cases ->
    TmMatch (substVar x s t)
      [(p, if x `Set.member` patternVars p then ti else substVar x s ti) | (p, ti) <- cases]

-- | Generate a fresh variable
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
