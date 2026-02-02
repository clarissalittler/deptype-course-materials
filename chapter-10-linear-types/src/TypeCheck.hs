{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( -- * Type checking
    typeCheck
  , typeOf
  , TypeError(..)
    -- * Type context
  , TypeContext
  , emptyContext
    -- * Usage tracking
  , Usage(..)
  , UsageEnv
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- =============================================================================
-- Usage Tracking
-- =============================================================================

-- | Usage count for a variable
data Usage
  = Unused     -- ^ Not yet used
  | UsedOnce   -- ^ Used exactly once
  | UsedMany   -- ^ Used more than once
  deriving (Eq, Show, Ord)

-- | Usage environment: maps variables to their usage count
type UsageEnv = Map Var Usage

-- | Combine two usage environments (for branches - takes max)
--
-- In if-then-else, both branches may use a variable, so we take max usage
combineUsage :: UsageEnv -> UsageEnv -> UsageEnv
combineUsage = Map.unionWith maxUsage
  where
    maxUsage Unused u = u
    maxUsage u Unused = u
    maxUsage UsedOnce UsedOnce = UsedOnce  -- Same usage in both branches
    maxUsage _ _ = UsedMany

-- | Add two usage environments (for sequential/parallel evaluation)
--
-- In pairs and application, both subterms are evaluated, so we add usages
addUsage :: UsageEnv -> UsageEnv -> UsageEnv
addUsage = Map.unionWith sumUsage
  where
    sumUsage Unused u = u
    sumUsage u Unused = u
    sumUsage _ _ = UsedMany  -- UsedOnce + UsedOnce = UsedMany

-- | Scale usage by multiplicity (for function application)
scaleUsage :: Mult -> UsageEnv -> UsageEnv
scaleUsage One = id
scaleUsage Many = Map.map scale
  where
    scale Unused = Unused
    scale UsedOnce = UsedMany
    scale UsedMany = UsedMany

-- | Increment usage of a variable
useVar :: Var -> UsageEnv -> UsageEnv
useVar x = Map.insertWith addUse x UsedOnce
  where
    addUse UsedOnce Unused = UsedOnce
    addUse UsedOnce UsedOnce = UsedMany
    addUse UsedOnce UsedMany = UsedMany
    addUse _ _ = UsedMany

-- =============================================================================
-- Type Context
-- =============================================================================

-- | Type context: maps variables to their types and multiplicities
type TypeContext = Map Var (Type, Mult)

-- | Empty typing context
emptyContext :: TypeContext
emptyContext = Map.empty

-- =============================================================================
-- Type Errors
-- =============================================================================

-- | Type errors in linear type checking
data TypeError
  = UnboundVariable Var
  | NotAFunction Type
  | ArgumentTypeMismatch Type Type
  | ConditionNotBool Type
  | BranchTypeMismatch Type Type
  | NotANat Type
  | NotAPair Type
  | NotABang Type
  | LinearVariableUnused Var
  | LinearVariableUsedTwice Var
  | LinearVariableUsedInBranch Var  -- Used in only one branch
  | UnrestrictedInLinearContext Var
  | TypeError String
  deriving (Eq)

instance Show TypeError where
  show = \case
    UnboundVariable x -> "Unbound variable: " ++ x
    NotAFunction ty -> "Expected function type, got: " ++ showType ty
    ArgumentTypeMismatch expected actual ->
      "Argument type mismatch: expected " ++ showType expected ++
      ", got " ++ showType actual
    ConditionNotBool ty -> "Condition must be Bool, got: " ++ showType ty
    BranchTypeMismatch t1 t2 ->
      "Branch types don't match: " ++ showType t1 ++ " vs " ++ showType t2
    NotANat ty -> "Expected Nat, got: " ++ showType ty
    NotAPair ty -> "Expected pair type, got: " ++ showType ty
    NotABang ty -> "Expected !-type, got: " ++ showType ty
    LinearVariableUnused x -> "Linear variable not used: " ++ x
    LinearVariableUsedTwice x -> "Linear variable used more than once: " ++ x
    LinearVariableUsedInBranch x ->
      "Linear variable used in only one branch: " ++ x
    UnrestrictedInLinearContext x ->
      "Unrestricted variable in linear context: " ++ x
    TypeError msg -> msg

showType :: Type -> String
showType = \case
  TyVar v -> v
  TyFun One t1 t2 -> "(" ++ showType t1 ++ " -o " ++ showType t2 ++ ")"
  TyFun Many t1 t2 -> "(" ++ showType t1 ++ " -> " ++ showType t2 ++ ")"
  TyBool -> "Bool"
  TyNat -> "Nat"
  TyUnit -> "()"
  TyPair t1 t2 -> "(" ++ showType t1 ++ " * " ++ showType t2 ++ ")"
  TyBang t -> "!" ++ showType t

-- =============================================================================
-- Linear Type Checking
-- =============================================================================

-- | Result of type checking includes the type and usage environment
type TypeResult = Either TypeError (Type, UsageEnv)

-- | Type check a closed term
typeCheck :: Term -> Either TypeError Type
typeCheck t = do
  (ty, usage) <- typeOf emptyContext t
  -- Check that all linear variables in scope were used
  checkFinalUsage usage
  return ty

-- | Check that no linear variables are left unused
checkFinalUsage :: UsageEnv -> Either TypeError ()
checkFinalUsage usage =
  case Map.toList (Map.filter (== Unused) usage) of
    [] -> Right ()
    ((x, _):_) -> Left $ LinearVariableUnused x

-- | Ensure linear variables are used consistently across branches
checkBranchUsage :: TypeContext -> UsageEnv -> UsageEnv -> Either TypeError ()
checkBranchUsage ctx usageLeft usageRight =
  case [x | (x, (_, One)) <- Map.toList ctx
          , used usageLeft x /= used usageRight x] of
    (x:_) -> Left $ LinearVariableUsedInBranch x
    [] -> Right ()
  where
    used env x = Map.findWithDefault Unused x env

-- | Type check a term in a context, returning type and usage
typeOf :: TypeContext -> Term -> TypeResult
typeOf ctx = \case
  -- Variables: mark as used
  Var x ->
    case Map.lookup x ctx of
      Just (ty, _mult) -> Right (ty, useVar x Map.empty)
      Nothing -> Left $ UnboundVariable x

  -- Lambda abstraction with multiplicity
  -- Γ, x:τ₁ ⊢ t : τ₂ ; Δ    x used according to m in Δ
  -- ─────────────────────────────────────────────────────
  -- Γ ⊢ λ(x :m τ₁). t : τ₁ -(m)-> τ₂ ; Δ \ x
  Lam x m ty1 t -> do
    let ctx' = Map.insert x (ty1, m) ctx
    (ty2, usage) <- typeOf ctx' t
    -- Check linear usage
    let xUsage = Map.findWithDefault Unused x usage
    case (m, xUsage) of
      (One, Unused) -> Left $ LinearVariableUnused x
      (One, UsedMany) -> Left $ LinearVariableUsedTwice x
      (Many, _) -> Right ()  -- Unrestricted can be used any amount
      (One, UsedOnce) -> Right ()
    Right (TyFun m ty1 ty2, Map.delete x usage)

  -- Application
  -- Γ ⊢ t₁ : τ₁ -(m)-> τ₂ ; Δ₁    Γ ⊢ t₂ : τ₁ ; Δ₂
  -- ─────────────────────────────────────────────────
  -- Γ ⊢ t₁ t₂ : τ₂ ; Δ₁ + m·Δ₂
  App t1 t2 -> do
    (ty1, usage1) <- typeOf ctx t1
    (ty2, usage2) <- typeOf ctx t2
    case ty1 of
      TyFun m argTy resTy ->
        if ty2 == argTy
          then Right (resTy, addUsage usage1 (scaleUsage m usage2))
          else Left $ ArgumentTypeMismatch argTy ty2
      _ -> Left $ NotAFunction ty1

  -- Booleans
  TmTrue -> Right (TyBool, Map.empty)
  TmFalse -> Right (TyBool, Map.empty)

  -- Conditional
  -- Linear variables must be used consistently in both branches
  TmIf t1 t2 t3 -> do
    (ty1, usage1) <- typeOf ctx t1
    case ty1 of
      TyBool -> do
        (ty2, usage2) <- typeOf ctx t2
        (ty3, usage3) <- typeOf ctx t3
        if ty2 == ty3
          then do
            checkBranchUsage ctx usage2 usage3
            -- Branches: take max (only one executes)
            -- Condition: add to result (always evaluates)
            let combinedBranch = combineUsage usage2 usage3
            Right (ty2, addUsage usage1 combinedBranch)
          else Left $ BranchTypeMismatch ty2 ty3
      _ -> Left $ ConditionNotBool ty1

  -- Natural numbers
  TmZero -> Right (TyNat, Map.empty)

  TmSucc t -> do
    (ty, usage) <- typeOf ctx t
    if ty == TyNat
      then Right (TyNat, usage)
      else Left $ NotANat ty

  TmPred t -> do
    (ty, usage) <- typeOf ctx t
    if ty == TyNat
      then Right (TyNat, usage)
      else Left $ NotANat ty

  TmIsZero t -> do
    (ty, usage) <- typeOf ctx t
    if ty == TyNat
      then Right (TyBool, usage)
      else Left $ NotANat ty

  -- Unit
  TmUnit -> Right (TyUnit, Map.empty)

  -- Pairs (tensor product)
  -- Γ ⊢ t₁ : τ₁ ; Δ₁    Γ ⊢ t₂ : τ₂ ; Δ₂
  -- ───────────────────────────────────────
  -- Γ ⊢ (t₁, t₂) : τ₁ * τ₂ ; Δ₁ + Δ₂
  TmPair t1 t2 -> do
    (ty1, usage1) <- typeOf ctx t1
    (ty2, usage2) <- typeOf ctx t2
    Right (TyPair ty1 ty2, addUsage usage1 usage2)

  -- Let-pair (tensor elimination)
  -- Γ ⊢ t₁ : τ₁ * τ₂ ; Δ₁    Γ, x:τ₁, y:τ₂ ⊢ t₂ : τ ; Δ₂
  -- ─────────────────────────────────────────────────────────
  -- Γ ⊢ let (x, y) = t₁ in t₂ : τ ; Δ₁ + Δ₂ \ {x, y}
  TmLetPair x y t1 t2 -> do
    (ty1, usage1) <- typeOf ctx t1
    case ty1 of
      TyPair tyA tyB -> do
        let ctx' = Map.insert x (tyA, One) $ Map.insert y (tyB, One) ctx
        (ty2, usage2) <- typeOf ctx' t2
        -- Check x and y are used exactly once
        let xUsage = Map.findWithDefault Unused x usage2
        let yUsage = Map.findWithDefault Unused y usage2
        case (xUsage, yUsage) of
          (UsedOnce, UsedOnce) -> Right ()
          (Unused, _) -> Left $ LinearVariableUnused x
          (_, Unused) -> Left $ LinearVariableUnused y
          (UsedMany, _) -> Left $ LinearVariableUsedTwice x
          (_, UsedMany) -> Left $ LinearVariableUsedTwice y
        let usage2' = Map.delete x $ Map.delete y usage2
        Right (ty2, addUsage usage1 usage2')
      _ -> Left $ NotAPair ty1

  -- Bang introduction
  -- Γ ⊢ t : τ ; ∅  (no linear resources used)
  -- ─────────────────────────────────────────
  -- Γ ⊢ !t : !τ ; ∅
  TmBang t -> do
    (ty, usage) <- typeOf ctx t
    -- Check no linear variables are used
    let linearUsed =
          [ x
          | (x, u) <- Map.toList usage
          , u /= Unused
          , Just (_, One) <- [Map.lookup x ctx]
          ]
    if null linearUsed
      then Right (TyBang ty, Map.empty)
      else Left $ TypeError ("Cannot use linear variables under !: " ++ head linearUsed)

  -- Bang elimination
  -- Γ ⊢ t₁ : !τ₁ ; Δ₁    Γ, x:τ₁ (unrestricted) ⊢ t₂ : τ₂ ; Δ₂
  -- ─────────────────────────────────────────────────────────────
  -- Γ ⊢ let !x = t₁ in t₂ : τ₂ ; Δ₁ + Δ₂
  TmLetBang x t1 t2 -> do
    (ty1, usage1) <- typeOf ctx t1
    case ty1 of
      TyBang tyA -> do
        let ctx' = Map.insert x (tyA, Many) ctx  -- x is unrestricted
        (ty2, usage2) <- typeOf ctx' t2
        let usage2' = Map.delete x usage2
        Right (ty2, addUsage usage1 usage2')
      _ -> Left $ NotABang ty1

  -- Let binding
  TmLet x m t1 t2 -> do
    (ty1, usage1) <- typeOf ctx t1
    let ctx' = Map.insert x (ty1, m) ctx
    (ty2, usage2) <- typeOf ctx' t2
    -- Check usage matches multiplicity
    let xUsage = Map.findWithDefault Unused x usage2
    case (m, xUsage) of
      (One, Unused) -> Left $ LinearVariableUnused x
      (One, UsedMany) -> Left $ LinearVariableUsedTwice x
      (Many, _) -> Right ()
      (One, UsedOnce) -> Right ()
    let usage2' = Map.delete x usage2
    Right (ty2, addUsage usage1 usage2')
