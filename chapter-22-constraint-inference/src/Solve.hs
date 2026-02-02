{-# LANGUAGE LambdaCase #-}

module Solve
  ( -- * Constraint solving
    solve
  , SolveError(..)
    -- * Unification
  , unify
  , unifyMany
    -- * Most general unifier
  , mgu
  ) where

import Syntax
import Constraint
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Control.Monad.Except

-- | Constraint solving errors
data SolveError
  = UnificationFail Type Type
  | OccursCheck TyVar Type
  | InfiniteType TyVar Type
  deriving (Eq, Show)

-- | Solve constraints using unification
-- Returns the most general unifier (MGU)
solve :: ConstraintSet -> Either SolveError Subst
solve = solveConstraints emptySubst
  where
    solveConstraints :: Subst -> ConstraintSet -> Either SolveError Subst
    solveConstraints s [] = return s
    solveConstraints s (c:cs) = case c of
      Equal t1 t2 -> do
        -- Apply current substitution to both types
        let t1' = applySubst s t1
        let t2' = applySubst s t2
        -- Unify
        s' <- unify t1' t2'
        -- Compose and continue
        let s'' = s' `composeSubst` s
        solveConstraints s'' cs

-- | Robinson's unification algorithm
unify :: Type -> Type -> Either SolveError Subst
unify t1 t2 | t1 == t2 = return emptySubst
unify (TyVar a) t = bindVar a t
unify t (TyVar a) = bindVar a t
unify (TyArr t1 t2) (TyArr t1' t2') = unifyMany [(t1, t1'), (t2, t2')]
unify (TyProd t1 t2) (TyProd t1' t2') = unifyMany [(t1, t1'), (t2, t2')]
unify (TyList t) (TyList t') = unify t t'
unify t1 t2 = throwError $ UnificationFail t1 t2

-- | Unify multiple pairs of types
unifyMany :: [(Type, Type)] -> Either SolveError Subst
unifyMany [] = return emptySubst
unifyMany ((t1, t2):rest) = do
  s1 <- unify t1 t2
  s2 <- unifyMany [(applySubst s1 t1', applySubst s1 t2') | (t1', t2') <- rest]
  return (s2 `composeSubst` s1)

-- | Bind a type variable to a type (with occurs check)
bindVar :: TyVar -> Type -> Either SolveError Subst
bindVar a t
  | t == TyVar a = return emptySubst
  | a `Set.member` freeTyVars t = throwError $ OccursCheck a t
  | otherwise = return $ Map.singleton a t

-- | Most general unifier
-- This is just an alias for unify for compatibility
mgu :: Type -> Type -> Either SolveError Subst
mgu = unify
