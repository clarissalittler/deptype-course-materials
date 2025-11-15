{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Syntax
  ( Var
  , Term(..)
  , freeVars
  , substVar
  , freshVar
  , alphaEq
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

-- | Variables are represented as strings
type Var = String

-- | Untyped lambda calculus terms
data Term
  = Var Var              -- ^ Variable
  | Lam Var Term         -- ^ Lambda abstraction: λx. t
  | App Term Term        -- ^ Application: t1 t2
  deriving (Eq, Show)

-- | Compute the set of free variables in a term
freeVars :: Term -> Set Var
freeVars = \case
  Var x -> Set.singleton x
  Lam x t -> Set.delete x (freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2

-- | Capture-avoiding substitution: substVar x s t replaces x with s in t
-- [x ↦ s]t
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y
    | y == x -> s
    | otherwise -> Var y
  Lam y t
    | y == x -> Lam y t  -- x is shadowed, don't substitute
    | y `Set.member` fvs ->
        -- y is free in s, need to rename y to avoid capture
        let y' = freshVar y (fvs `Set.union` freeVars t)
            t' = substVar y (Var y') t
        in Lam y' (substVar x s t')
    | otherwise -> Lam y (substVar x s t)
    where
      fvs = freeVars s
  App t1 t2 -> App (substVar x s t1) (substVar x s t2)

-- | Generate a fresh variable name that doesn't appear in the given set
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]

-- | Alpha equivalence: two terms are equal up to renaming of bound variables
-- We check equivalence under a context mapping variables from the first term
-- to variables in the second term
alphaEq :: Term -> Term -> Bool
alphaEq = go []
  where
    go :: [(Var, Var)] -> Term -> Term -> Bool
    go ctx (Var x) (Var y) =
      case lookup x ctx of
        Just y' -> y == y'
        Nothing -> x == y  -- Both free variables must be the same
    go ctx (Lam x t1) (Lam y t2) =
      go ((x, y) : ctx) t1 t2
    go ctx (App t1 t2) (App t1' t2') =
      go ctx t1 t1' && go ctx t2 t2'
    go _ _ _ = False
