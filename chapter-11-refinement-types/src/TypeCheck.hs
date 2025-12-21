{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( -- * Type checking
    typeCheck
  , checkType
  , infer
    -- * Subtyping
  , isSubtype
    -- * Errors
  , TypeError(..)
    -- * Context
  , Context
  , emptyContext
    -- * Predicate validity
  , isValid
  , implies
  ) where

import Syntax
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set

-- =============================================================================
-- Type Errors
-- =============================================================================

data TypeError
  = UnboundVariable Var
  | TypeMismatch Type Type
  | ExpectedFunction Type
  | ExpectedRefinement Type
  | InvalidPredicate String
  | SubtypingFailure Type Type
  | ArithmeticOnNonNat Type
  | ConditionNotBool Type
  deriving (Eq, Show)

-- =============================================================================
-- Context
-- =============================================================================

-- | Type context: variable -> type
type TypeEnv = Map Var Type

-- | Path condition: accumulated predicates from branches
type PathCondition = [Pred]

-- | Full context for type checking
data Context = Context
  { ctxTypes :: TypeEnv
  , ctxPath  :: PathCondition
  }

emptyContext :: Context
emptyContext = Context Map.empty []

-- | Add a variable binding
bindVar :: Var -> Type -> Context -> Context
bindVar x ty ctx = ctx { ctxTypes = Map.insert x ty (ctxTypes ctx) }

-- | Add a path condition
addCondition :: Pred -> Context -> Context
addCondition p ctx = ctx { ctxPath = p : ctxPath ctx }

-- | Look up a variable
lookupVar :: Var -> Context -> Maybe Type
lookupVar x ctx = Map.lookup x (ctxTypes ctx)

-- =============================================================================
-- Type Checking
-- =============================================================================

-- | Type check a term, returning its type or an error
typeCheck :: Term -> Either TypeError Type
typeCheck = infer emptyContext

-- | Check that a term has a specific type
checkType :: Context -> Term -> Type -> Either TypeError ()
checkType ctx t ty = do
  ty' <- infer ctx t
  if isSubtype ctx ty' ty
    then Right ()
    else Left $ SubtypingFailure ty' ty

-- | Infer the type of a term
infer :: Context -> Term -> Either TypeError Type
infer ctx = \case
  Var x ->
    case lookupVar x ctx of
      Nothing -> Left $ UnboundVariable x
      Just ty -> Right ty

  Lam x ty1 t -> do
    ty2 <- infer (bindVar x ty1 ctx) t
    Right $ TyFun x ty1 ty2

  App t1 t2 -> do
    ty1 <- infer ctx t1
    case ty1 of
      TyFun x tyArg tyResult -> do
        checkType ctx t2 tyArg
        -- Substitute argument in result type if it mentions x
        Right $ substType x t2 tyResult
      _ -> Left $ ExpectedFunction ty1

  TmTrue -> Right $ TyBase TyBool
  TmFalse -> Right $ TyBase TyBool

  TmIf t1 t2 t3 -> do
    ty1 <- infer ctx t1
    case stripRefinement ty1 of
      TyBase TyBool -> do
        -- In then-branch, assume condition is true
        let ctx2 = addCondition (termToPred t1) ctx
        ty2 <- infer ctx2 t2
        -- In else-branch, assume condition is false
        let ctx3 = addCondition (PNot (termToPred t1)) ctx
        ty3 <- infer ctx3 t3
        -- Join the types
        case joinTypes ctx ty2 ty3 of
          Just ty -> Right ty
          Nothing -> Left $ TypeMismatch ty2 ty3
      _ -> Left $ ConditionNotBool ty1

  TmZero -> Right $ TyBase TyNat

  TmSucc t -> do
    ty <- infer ctx t
    case stripRefinement ty of
      TyBase TyNat -> Right $ TyBase TyNat
      _ -> Left $ ArithmeticOnNonNat ty

  TmPred t -> do
    ty <- infer ctx t
    case stripRefinement ty of
      TyBase TyNat -> Right $ TyBase TyNat
      _ -> Left $ ArithmeticOnNonNat ty

  TmIsZero t -> do
    ty <- infer ctx t
    case stripRefinement ty of
      TyBase TyNat -> Right $ TyBase TyBool
      _ -> Left $ ArithmeticOnNonNat ty

  TmArith _ t1 t2 -> do
    ty1 <- infer ctx t1
    ty2 <- infer ctx t2
    case (stripRefinement ty1, stripRefinement ty2) of
      (TyBase TyNat, TyBase TyNat) -> Right $ TyBase TyNat
      (TyBase TyNat, _) -> Left $ ArithmeticOnNonNat ty2
      _ -> Left $ ArithmeticOnNonNat ty1

  TmUnit -> Right $ TyBase TyUnit

  TmLet x t1 t2 -> do
    ty1 <- infer ctx t1
    -- Create a refined type for x based on the binding
    let refinedTy = refineBinding x t1 ty1
    infer (bindVar x refinedTy ctx) t2

  TmAscribe t ty -> do
    checkType ctx t ty
    Right ty

-- =============================================================================
-- Subtyping
-- =============================================================================

-- | Check if ty1 is a subtype of ty2 under the given context
--
-- Key rule for refinements:
--   {x: T | φ} <: {x: T | ψ}  iff  ∀x. φ(x) => ψ(x)
--
-- This is the core of refinement type checking!
isSubtype :: Context -> Type -> Type -> Bool
isSubtype ctx ty1 ty2 = case (ty1, ty2) of
  -- Same base types
  (TyBase b1, TyBase b2) -> b1 == b2

  -- Base type is subtype of refinement with true predicate
  (TyBase b1, TyRefine _ (TyBase b2) PTrue) -> b1 == b2

  -- Refinement is subtype of base (drop refinement)
  (TyRefine _ t _, TyBase b) ->
    case stripRefinement t of
      TyBase b' -> b == b'
      _ -> False

  -- Refinement subtyping: check predicate implication
  (TyRefine x1 t1 p1, TyRefine x2 t2 p2) ->
    isSubtype ctx t1 t2 &&
    -- Check: path ∧ p1 => p2[x1/x2]
    let p2' = if x1 == x2 then p2 else substPred x2 (PAVar x1) p2
        assumptions = PAnd (pathToPred ctx) p1
    in implies assumptions p2'

  -- Refinement vs base
  (TyRefine _ t _, ty2') ->
    isSubtype ctx (stripRefinement t) ty2'

  (ty1', TyRefine _ t p) ->
    isSubtype ctx ty1' (stripRefinement t) &&
    -- Check if path implies the predicate (trivially satisfied)
    (p == PTrue || implies (pathToPred ctx) p)

  -- Function subtyping (contravariant in arg, covariant in result)
  (TyFun x1 argTy1 resTy1, TyFun x2 argTy2 resTy2) ->
    isSubtype ctx argTy2 argTy1 &&  -- contravariant
    let ctx' = bindVar x2 argTy2 ctx
        resTy1' = if x1 == x2 then resTy1 else substTypeVar x1 x2 resTy1
    in isSubtype ctx' resTy1' resTy2  -- covariant

  _ -> False

-- =============================================================================
-- Predicate Validity / Implication
-- =============================================================================

-- | Check if a predicate is valid (always true)
isValid :: Pred -> Bool
isValid = \case
  PTrue -> True
  PFalse -> False
  PAnd p1 p2 -> isValid p1 && isValid p2
  POr p1 p2 -> isValid p1 || isValid p2
  PImpl p1 p2 -> not (isSatisfiable (PAnd p1 (PNot p2)))
  PNot p -> not (isSatisfiable p)
  PVar _ -> False  -- Variable alone isn't valid
  PComp op a1 a2 -> evalCompOp op a1 a2

-- | Check if a predicate is satisfiable
isSatisfiable :: Pred -> Bool
isSatisfiable = \case
  PTrue -> True
  PFalse -> False
  PAnd p1 p2 -> isSatisfiable p1 && isSatisfiable p2
  POr p1 p2 -> isSatisfiable p1 || isSatisfiable p2
  PImpl p1 p2 -> isSatisfiable (POr (PNot p1) p2)
  PNot p -> not (isValid p)
  PVar _ -> True  -- Variable could be true
  PComp _ _ _ -> True  -- Comparisons might be satisfiable

-- | Check if p1 implies p2
implies :: Pred -> Pred -> Bool
implies p1 p2 = isValid (PImpl p1 p2)

-- | Evaluate comparison of ground arithmetic terms
evalCompOp :: CompOp -> PArith -> PArith -> Bool
evalCompOp op a1 a2 =
  case (evalArith a1, evalArith a2) of
    (Just n1, Just n2) -> case op of
      OpEq  -> n1 == n2
      OpNeq -> n1 /= n2
      OpLt  -> n1 < n2
      OpLe  -> n1 <= n2
      OpGt  -> n1 > n2
      OpGe  -> n1 >= n2
    _ -> False  -- Can't evaluate if variables present

-- | Try to evaluate an arithmetic expression to a constant
evalArith :: PArith -> Maybe Int
evalArith = \case
  PAVar _ -> Nothing  -- Has variables
  PALit n -> Just n
  PAAdd a1 a2 -> (+) <$> evalArith a1 <*> evalArith a2
  PASub a1 a2 -> (-) <$> evalArith a1 <*> evalArith a2
  PAMul n a -> (n *) <$> evalArith a

-- =============================================================================
-- Helper Functions
-- =============================================================================

-- | Strip refinement to get underlying type
stripRefinement :: Type -> Type
stripRefinement = \case
  TyRefine _ t _ -> stripRefinement t
  t -> t

-- | Get the base type if this is a simple base or refined base type
getBaseType :: Type -> Maybe BaseType
getBaseType = \case
  TyBase b -> Just b
  TyRefine _ t _ -> getBaseType t
  _ -> Nothing

-- | Convert path condition to a single predicate
pathToPred :: Context -> Pred
pathToPred ctx = case ctxPath ctx of
  [] -> PTrue
  ps -> foldr1 PAnd ps

-- | Try to convert a boolean term to a predicate
termToPred :: Term -> Pred
termToPred = \case
  Var x -> PVar x
  TmTrue -> PTrue
  TmFalse -> PFalse
  TmIsZero t ->
    case termToArith t of
      Just a -> PComp OpEq a (PALit 0)
      Nothing -> PTrue  -- Conservative approximation
  _ -> PTrue  -- Conservative: assume true

-- | Try to convert a numeric term to arithmetic expression
termToArith :: Term -> Maybe PArith
termToArith = \case
  Var x -> Just $ PAVar x
  TmZero -> Just $ PALit 0
  TmSucc t -> do
    a <- termToArith t
    Just $ PAAdd a (PALit 1)
  TmPred t -> do
    a <- termToArith t
    Just $ PASub a (PALit 1)
  TmArith Add t1 t2 -> do
    a1 <- termToArith t1
    a2 <- termToArith t2
    Just $ PAAdd a1 a2
  TmArith Sub t1 t2 -> do
    a1 <- termToArith t1
    a2 <- termToArith t2
    Just $ PASub a1 a2
  _ -> Nothing

-- | Create a refined type for a let binding
refineBinding :: Var -> Term -> Type -> Type
refineBinding x t ty =
  case termToArith t of
    Just a -> TyRefine x ty (PComp OpEq (PAVar x) a)
    Nothing -> ty

-- | Join two types (find common supertype)
joinTypes :: Context -> Type -> Type -> Maybe Type
joinTypes ctx ty1 ty2
  | isSubtype ctx ty1 ty2 = Just ty2
  | isSubtype ctx ty2 ty1 = Just ty1
  | otherwise = case (ty1, ty2) of
      (TyRefine x1 t1 p1, TyRefine _ t2 p2) ->
        case joinTypes ctx t1 t2 of
          Just t -> Just $ TyRefine x1 t (POr p1 p2)
          Nothing -> Nothing
      (TyRefine _ t _, ty2') -> joinTypes ctx t ty2'
      (ty1', TyRefine _ t _) -> joinTypes ctx ty1' t
      _ -> Nothing

-- | Substitute a term for a variable in a type
substType :: Var -> Term -> Type -> Type
substType x t = \case
  TyBase b -> TyBase b
  TyRefine y ty p
    | y == x -> TyRefine y ty p  -- Shadowed
    | otherwise ->
        let p' = case termToArith t of
              Just a -> substPred x a p
              Nothing -> p
        in TyRefine y (substType x t ty) p'
  TyFun y ty1 ty2
    | y == x -> TyFun y (substType x t ty1) ty2  -- Shadowed in result
    | otherwise -> TyFun y (substType x t ty1) (substType x t ty2)

-- | Substitute a variable for another variable in a type
substTypeVar :: Var -> Var -> Type -> Type
substTypeVar x y = \case
  TyBase b -> TyBase b
  TyRefine z ty p
    | z == x -> TyRefine z ty p  -- Shadowed
    | otherwise -> TyRefine z (substTypeVar x y ty) (substPred x (PAVar y) p)
  TyFun z ty1 ty2
    | z == x -> TyFun z (substTypeVar x y ty1) ty2
    | otherwise -> TyFun z (substTypeVar x y ty1) (substTypeVar x y ty2)
