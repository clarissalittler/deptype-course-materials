{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Infer
  ( -- * Type inference
    infer
  , inferType
  , TypeError(..)
    -- * Substitutions
  , Subst
  , emptySubst
  , composeSubst
    -- * Type environment
  , TypeEnv
  , emptyEnv
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.State
import Control.Monad.Except

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

-- | Type errors
data TypeError
  = UnboundVariable Var
  | UnificationFail Type Type
  | OccursCheck TyVar Type
  | TypeMismatch Type Type
  deriving (Eq, Show)

-- | Inference monad
newtype Infer a = Infer (ExceptT TypeError (State Int) a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadError TypeError)

-- | Run inference
runInfer :: Infer a -> Either TypeError a
runInfer (Infer m) = evalState (runExceptT m) 0

-- | Generate fresh type variable
fresh :: Infer Type
fresh = do
  n <- get
  put (n + 1)
  return $ TyVar ("t" ++ show n)

-- | Instantiate a type scheme by replacing bound variables with fresh type variables
instantiate :: TypeScheme -> Infer Type
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

-- | Robinson's unification algorithm
unify :: Type -> Type -> Infer Subst
unify t1 t2 | t1 == t2 = return emptySubst
unify (TyVar a) t = bindVar a t
unify t (TyVar a) = bindVar a t
unify (TyArr t1 t2) (TyArr t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applySubst s1 t2) (applySubst s1 t2')
  return (s2 `composeSubst` s1)
unify (TyProd t1 t2) (TyProd t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applySubst s1 t2) (applySubst s1 t2')
  return (s2 `composeSubst` s1)
unify (TyList t) (TyList t') = unify t t'
unify t1 t2 = throwError $ UnificationFail t1 t2

-- | Bind a type variable to a type (occurs check)
bindVar :: TyVar -> Type -> Infer Subst
bindVar a t
  | t == TyVar a = return emptySubst
  | a `Set.member` freeTyVars t = throwError $ OccursCheck a t
  | otherwise = return $ Map.singleton a t

-- | Type inference (Algorithm W)
inferType :: TypeEnv -> Term -> Infer (Subst, Type)
inferType env = \case
  -- Variable
  Var x -> case Map.lookup x (case env of TypeEnv m -> m) of
    Nothing -> throwError $ UnboundVariable x
    Just scheme -> do
      ty <- instantiate scheme
      return (emptySubst, ty)

  -- Lambda abstraction
  Lam x body -> do
    tv <- fresh
    let env' = extendEnv x (TypeScheme [] tv) env
    (s, bodyTy) <- inferType env' body
    return (s, TyArr (applySubst s tv) bodyTy)

  -- Application
  App t1 t2 -> do
    (s1, ty1) <- inferType env t1
    (s2, ty2) <- inferType (applySubstEnv s1 env) t2
    tv <- fresh
    s3 <- unify (applySubst s2 ty1) (TyArr ty2 tv)
    return (s3 `composeSubst` s2 `composeSubst` s1, applySubst s3 tv)

  -- Let (with polymorphism!)
  Let x t1 t2 -> do
    (s1, ty1) <- inferType env t1
    let env' = applySubstEnv s1 env
        scheme = generalize env' ty1
        env'' = extendEnv x scheme env'
    (s2, ty2) <- inferType env'' t2
    return (s2 `composeSubst` s1, ty2)

  -- Booleans
  TmTrue -> return (emptySubst, TyBool)
  TmFalse -> return (emptySubst, TyBool)
  TmIf t1 t2 t3 -> do
    (s1, ty1) <- inferType env t1
    s2 <- unify ty1 TyBool
    let s = s2 `composeSubst` s1
    (s3, ty2) <- inferType (applySubstEnv s env) t2
    (s4, ty3) <- inferType (applySubstEnv (s3 `composeSubst` s) env) t3
    s5 <- unify (applySubst s4 ty2) ty3
    let finalSubst = s5 `composeSubst` s4 `composeSubst` s3 `composeSubst` s
    return (finalSubst, applySubst s5 ty3)

  -- Natural numbers
  TmZero -> return (emptySubst, TyNat)
  TmSucc t -> do
    (s, ty) <- inferType env t
    s' <- unify ty TyNat
    return (s' `composeSubst` s, TyNat)
  TmPred t -> do
    (s, ty) <- inferType env t
    s' <- unify ty TyNat
    return (s' `composeSubst` s, TyNat)
  TmIsZero t -> do
    (s, ty) <- inferType env t
    s' <- unify ty TyNat
    return (s' `composeSubst` s, TyBool)

  -- Pairs
  TmPair t1 t2 -> do
    (s1, ty1) <- inferType env t1
    (s2, ty2) <- inferType (applySubstEnv s1 env) t2
    return (s2 `composeSubst` s1, TyProd (applySubst s2 ty1) ty2)

  TmFst t -> do
    (s, ty) <- inferType env t
    tv1 <- fresh
    tv2 <- fresh
    s' <- unify ty (TyProd tv1 tv2)
    return (s' `composeSubst` s, applySubst s' tv1)

  TmSnd t -> do
    (s, ty) <- inferType env t
    tv1 <- fresh
    tv2 <- fresh
    s' <- unify ty (TyProd tv1 tv2)
    return (s' `composeSubst` s, applySubst s' tv2)

  -- Lists
  TmNil -> do
    tv <- fresh
    return (emptySubst, TyList tv)

  TmCons t1 t2 -> do
    (s1, ty1) <- inferType env t1
    (s2, ty2) <- inferType (applySubstEnv s1 env) t2
    tv <- fresh
    s3 <- unify ty2 (TyList tv)
    s4 <- unify (applySubst s3 ty1) (applySubst s3 tv)
    let s = s4 `composeSubst` s3 `composeSubst` s2 `composeSubst` s1
    return (s, applySubst s4 ty2)

  TmIsNil t -> do
    (s, ty) <- inferType env t
    tv <- fresh
    s' <- unify ty (TyList tv)
    return (s' `composeSubst` s, TyBool)

  TmHead t -> do
    (s, ty) <- inferType env t
    tv <- fresh
    s' <- unify ty (TyList tv)
    return (s' `composeSubst` s, applySubst s' tv)

  TmTail t -> do
    (s, ty) <- inferType env t
    tv <- fresh
    s' <- unify ty (TyList tv)
    return (s' `composeSubst` s, ty)

-- | Main inference function for closed terms
infer :: Term -> Either TypeError Type
infer t = do
  (s, ty) <- runInfer (inferType emptyEnv t)
  return (applySubst s ty)
