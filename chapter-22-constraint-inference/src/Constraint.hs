{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Constraint
  ( -- * Constraints
    Constraint(..)
  , ConstraintSet
    -- * Constraint generation
  , generateConstraints
  , ConstraintError(..)
    -- * Type environment
  , TypeEnv
  , emptyEnv
  , extendEnv
  , removeEnv
    -- * Substitutions
  , Subst
  , emptySubst
  , applySubst
  , applySubstEnv
  , composeSubst
    -- * Type scheme operations
  , instantiate
  , generalize
  , freeTyVarsEnv
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.State
import Control.Monad.Except

-- | Type constraints
data Constraint
  = Equal Type Type           -- ^ τ₁ ≡ τ₂
  deriving (Eq, Show)

-- | Set of constraints
type ConstraintSet = [Constraint]

-- | Type substitution: maps type variables to types
type Subst = Map TyVar Type

-- | Empty substitution
emptySubst :: Subst
emptySubst = Map.empty

-- | Compose substitutions (s1 ∘ s2)
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.map (applySubst s1) s2 `Map.union` s1

-- | Apply substitution to a type
applySubst :: Subst -> Type -> Type
applySubst s = \case
  TyVar a -> Map.findWithDefault (TyVar a) a s
  TyArr t1 t2 -> TyArr (applySubst s t1) (applySubst s t2)
  TyBool -> TyBool
  TyNat -> TyNat
  TyProd t1 t2 -> TyProd (applySubst s t1) (applySubst s t2)
  TyList t -> TyList (applySubst s t)

-- | Apply substitution to a type scheme
applySubstScheme :: Subst -> TypeScheme -> TypeScheme
applySubstScheme s (TypeScheme vars ty) =
  TypeScheme vars (applySubst (foldr Map.delete s vars) ty)

-- | Type environment: maps variables to type schemes
newtype TypeEnv = TypeEnv (Map Var TypeScheme)
  deriving (Show)

-- | Empty environment
emptyEnv :: TypeEnv
emptyEnv = TypeEnv Map.empty

-- | Extend environment
extendEnv :: Var -> TypeScheme -> TypeEnv -> TypeEnv
extendEnv x scheme (TypeEnv env) = TypeEnv (Map.insert x scheme env)

-- | Remove variable from environment
removeEnv :: Var -> TypeEnv -> TypeEnv
removeEnv x (TypeEnv env) = TypeEnv (Map.delete x env)

-- | Apply substitution to environment
applySubstEnv :: Subst -> TypeEnv -> TypeEnv
applySubstEnv s (TypeEnv env) = TypeEnv (Map.map (applySubstScheme s) env)

-- | Free type variables in environment
freeTyVarsEnv :: TypeEnv -> Set TyVar
freeTyVarsEnv (TypeEnv env) =
  Set.unions [freeTyVarsScheme scheme | scheme <- Map.elems env]

-- | Free type variables in type scheme
freeTyVarsScheme :: TypeScheme -> Set TyVar
freeTyVarsScheme (TypeScheme vars ty) = freeTyVars ty Set.\\ Set.fromList vars

-- | Constraint generation errors
data ConstraintError
  = UnboundVariable Var
  deriving (Eq, Show)

-- | Constraint generation monad
newtype ConstraintGen a = ConstraintGen
  (ExceptT ConstraintError (State Int) a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadError ConstraintError)

-- | Run constraint generation
runConstraintGen :: ConstraintGen a -> Either ConstraintError a
runConstraintGen (ConstraintGen m) = evalState (runExceptT m) 0

-- | Generate fresh type variable
fresh :: ConstraintGen Type
fresh = do
  n <- get
  put (n + 1)
  return $ TyVar ("t" ++ show n)

-- | Instantiate a type scheme by replacing bound variables with fresh type variables
instantiate :: TypeScheme -> ConstraintGen Type
instantiate (TypeScheme vars ty) = do
  freshVars <- mapM (const fresh) vars
  let s = Map.fromList (zip vars freshVars)
  return $ applySubst s ty

-- | Generalize a type to a type scheme
-- ∀ (ftv(τ) \ ftv(Γ)). τ
generalize :: TypeEnv -> Type -> TypeScheme
generalize env ty =
  let vars = Set.toList (freeTyVars ty Set.\\ freeTyVarsEnv env)
  in TypeScheme vars ty

-- | Generate constraints from a term
-- Returns (constraints, inferred type)
generateConstraintsFrom :: TypeEnv -> Term -> ConstraintGen (ConstraintSet, Type)
generateConstraintsFrom env = \case
  -- Variable
  Var x -> case Map.lookup x (case env of TypeEnv m -> m) of
    Nothing -> throwError $ UnboundVariable x
    Just scheme -> do
      ty <- instantiate scheme
      return ([], ty)

  -- Lambda abstraction
  Lam x body -> do
    tv <- fresh
    let env' = extendEnv x (TypeScheme [] tv) env
    (constraints, bodyTy) <- generateConstraintsFrom env' body
    return (constraints, TyArr tv bodyTy)

  -- Application
  App t1 t2 -> do
    (c1, ty1) <- generateConstraintsFrom env t1
    (c2, ty2) <- generateConstraintsFrom env t2
    tv <- fresh
    let c3 = [Equal ty1 (TyArr ty2 tv)]
    return (c1 ++ c2 ++ c3, tv)

  -- Let (with polymorphism!)
  Let x t1 t2 -> do
    (c1, ty1) <- generateConstraintsFrom env t1
    -- For proper let-polymorphism, we need to generalize after solving c1
    -- For now, we use a simpler approach: generalize immediately
    let scheme = generalize env ty1
        env' = extendEnv x scheme env
    (c2, ty2) <- generateConstraintsFrom env' t2
    return (c1 ++ c2, ty2)

  -- Booleans
  TmTrue -> return ([], TyBool)
  TmFalse -> return ([], TyBool)
  TmIf t1 t2 t3 -> do
    (c1, ty1) <- generateConstraintsFrom env t1
    (c2, ty2) <- generateConstraintsFrom env t2
    (c3, ty3) <- generateConstraintsFrom env t3
    let constraints = c1 ++ c2 ++ c3 ++
                      [Equal ty1 TyBool, Equal ty2 ty3]
    return (constraints, ty2)

  -- Natural numbers
  TmZero -> return ([], TyNat)
  TmSucc t -> do
    (c, ty) <- generateConstraintsFrom env t
    return (c ++ [Equal ty TyNat], TyNat)
  TmPred t -> do
    (c, ty) <- generateConstraintsFrom env t
    return (c ++ [Equal ty TyNat], TyNat)
  TmIsZero t -> do
    (c, ty) <- generateConstraintsFrom env t
    return (c ++ [Equal ty TyNat], TyBool)

  -- Pairs
  TmPair t1 t2 -> do
    (c1, ty1) <- generateConstraintsFrom env t1
    (c2, ty2) <- generateConstraintsFrom env t2
    return (c1 ++ c2, TyProd ty1 ty2)

  TmFst t -> do
    (c, ty) <- generateConstraintsFrom env t
    tv1 <- fresh
    tv2 <- fresh
    return (c ++ [Equal ty (TyProd tv1 tv2)], tv1)

  TmSnd t -> do
    (c, ty) <- generateConstraintsFrom env t
    tv1 <- fresh
    tv2 <- fresh
    return (c ++ [Equal ty (TyProd tv1 tv2)], tv2)

  -- Lists
  TmNil -> do
    tv <- fresh
    return ([], TyList tv)

  TmCons t1 t2 -> do
    (c1, ty1) <- generateConstraintsFrom env t1
    (c2, ty2) <- generateConstraintsFrom env t2
    tv <- fresh
    let constraints = c1 ++ c2 ++
                      [Equal ty2 (TyList tv), Equal ty1 tv]
    return (constraints, TyList tv)

  TmIsNil t -> do
    (c, ty) <- generateConstraintsFrom env t
    tv <- fresh
    return (c ++ [Equal ty (TyList tv)], TyBool)

  TmHead t -> do
    (c, ty) <- generateConstraintsFrom env t
    tv <- fresh
    return (c ++ [Equal ty (TyList tv)], tv)

  TmTail t -> do
    (c, ty) <- generateConstraintsFrom env t
    tv <- fresh
    return (c ++ [Equal ty (TyList tv)], TyList tv)

-- | Generate constraints from a closed term
generateConstraints :: Term -> Either ConstraintError (ConstraintSet, Type)
generateConstraints t = runConstraintGen (generateConstraintsFrom emptyEnv t)
