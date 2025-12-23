{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( -- * Type checking
    typeCheck
  , typeOf
  , TypeError(..)
    -- * Subtyping
  , isSubtype
  , (<:)
    -- * Join and Meet
  , join
  , meet
    -- * Type context
  , TypeContext
  , emptyContext
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.List (intercalate)

-- | Type context: maps variables to their types
type TypeContext = Map Var Type

-- | Empty typing context
emptyContext :: TypeContext
emptyContext = Map.empty

-- | Type errors
data TypeError
  = UnboundVariable Var
  | NotAFunction Type
  | ArgumentTypeMismatch Type Type  -- expected, actual
  | ConditionNotBool Type
  | BranchTypeMismatch Type Type
  | NotANat Type
  | NotARecord Type
  | FieldNotFound Label Type
  | SubtypingError Type Type  -- expected supertype, actual type
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
    NotARecord ty -> "Expected record type, got: " ++ showType ty
    FieldNotFound l ty -> "Field '" ++ l ++ "' not found in: " ++ showType ty
    SubtypingError sup sub ->
      "Type " ++ showType sub ++ " is not a subtype of " ++ showType sup
    TypeError msg -> msg

showType :: Type -> String
showType = \case
  TyVar v -> v
  TyArr t1 t2 -> "(" ++ showType t1 ++ " -> " ++ showType t2 ++ ")"
  TyBool -> "Bool"
  TyNat -> "Nat"
  TyTop -> "Top"
  TyBot -> "Bot"
  TyRecord fields ->
    "{" ++ intercalate ", " [l ++ ": " ++ showType t | (l, t) <- Map.toList fields] ++ "}"

-- =============================================================================
-- Subtyping
-- =============================================================================

-- | Subtyping relation: τ₁ <: τ₂ means τ₁ is a subtype of τ₂
--
-- Rules:
-- 1. Reflexivity: τ <: τ
-- 2. Transitivity: if τ₁ <: τ₂ and τ₂ <: τ₃ then τ₁ <: τ₃
-- 3. Top: τ <: Top (for all τ)
-- 4. Bottom: Bot <: τ (for all τ)
-- 5. Arrow: if τ₁ <: σ₁ and σ₂ <: τ₂ then (σ₁ → σ₂) <: (τ₁ → τ₂)
--    (contravariant in argument, covariant in result)
-- 6. Record width: {l₁:τ₁, ..., lₙ:τₙ, lₙ₊₁:τₙ₊₁} <: {l₁:τ₁, ..., lₙ:τₙ}
--    (more fields is a subtype)
-- 7. Record depth: if τᵢ <: σᵢ for all i, then {lᵢ:τᵢ} <: {lᵢ:σᵢ}
--    (fields can be subtypes)
isSubtype :: Type -> Type -> Bool
isSubtype t1 t2 = t1 <: t2

-- | Infix subtyping operator
(<:) :: Type -> Type -> Bool
(<:) = subtype

-- | Core subtyping algorithm
subtype :: Type -> Type -> Bool
subtype t1 t2
  -- Reflexivity
  | t1 == t2 = True
  -- Top is supertype of everything
  | TyTop <- t2 = True
  -- Bot is subtype of everything
  | TyBot <- t1 = True
  -- Function subtyping (contravariant in arg, covariant in result)
  | TyArr s1 s2 <- t1
  , TyArr u1 u2 <- t2
  = subtype u1 s1 && subtype s2 u2  -- Note: u1 <: s1, not s1 <: u1!
  -- Record subtyping (width + depth)
  | TyRecord fields1 <- t1
  , TyRecord fields2 <- t2
  = recordSubtype fields1 fields2
  -- Base types only equal to themselves (handled by reflexivity)
  | otherwise = False

-- | Record subtyping: {more fields} <: {fewer fields}
-- AND each common field must be a subtype
recordSubtype :: Map Label Type -> Map Label Type -> Bool
recordSubtype sub sup =
  -- For each field in supertype, subtype must have it with subtype relation
  all checkField (Map.toList sup)
  where
    checkField (label, supTy) =
      case Map.lookup label sub of
        Nothing -> False  -- Missing field
        Just subTy -> subtype subTy supTy  -- Depth subtyping

-- =============================================================================
-- Type Checking with Subsumption
-- =============================================================================

-- | Type check a closed term
typeCheck :: Term -> Either TypeError Type
typeCheck = typeOf emptyContext

-- | Type check a term in a context
--
-- Key rule: SUBSUMPTION (T-Sub)
--   If Γ ⊢ t : S and S <: T, then Γ ⊢ t : T
--
-- This allows implicit upcasting: if we have a value of type S
-- and S is a subtype of T, we can use it where T is expected.
typeOf :: TypeContext -> Term -> Either TypeError Type
typeOf ctx = \case
  -- Variables
  Var x ->
    case Map.lookup x ctx of
      Just ty -> Right ty
      Nothing -> Left $ UnboundVariable x

  -- Lambda abstraction
  -- Γ, x:τ₁ ⊢ t : τ₂
  -- ─────────────────────
  -- Γ ⊢ λx:τ₁. t : τ₁ → τ₂
  Lam x ty1 t -> do
    ty2 <- typeOf (Map.insert x ty1 ctx) t
    Right $ TyArr ty1 ty2

  -- Application with subsumption
  -- Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : σ    σ <: τ₁
  -- ───────────────────────────────────────────
  -- Γ ⊢ t₁ t₂ : τ₂
  App t1 t2 -> do
    ty1 <- typeOf ctx t1
    ty2 <- typeOf ctx t2
    case ty1 of
      TyArr argTy resTy ->
        if ty2 <: argTy
          then Right resTy
          else Left $ SubtypingError argTy ty2
      TyBot -> Right TyBot  -- Bot applied to anything is Bot
      _ -> Left $ NotAFunction ty1

  -- Booleans
  TmTrue -> Right TyBool
  TmFalse -> Right TyBool

  -- Conditional: branches must have a common supertype
  -- We use the JOIN (least upper bound) of the branch types
  TmIf t1 t2 t3 -> do
    ty1 <- typeOf ctx t1
    case ty1 of
      TyBool -> do
        ty2 <- typeOf ctx t2
        ty3 <- typeOf ctx t3
        case join ty2 ty3 of
          Just ty -> Right ty
          Nothing -> Left $ BranchTypeMismatch ty2 ty3
      _ -> Left $ ConditionNotBool ty1

  -- Natural numbers
  TmZero -> Right TyNat

  TmSucc t -> do
    ty <- typeOf ctx t
    if ty <: TyNat
      then Right TyNat
      else Left $ NotANat ty

  TmPred t -> do
    ty <- typeOf ctx t
    if ty <: TyNat
      then Right TyNat
      else Left $ NotANat ty

  TmIsZero t -> do
    ty <- typeOf ctx t
    if ty <: TyNat
      then Right TyBool
      else Left $ NotANat ty

  -- Records
  TmRecord fields -> do
    fieldTypes <- traverse (typeOf ctx) fields
    Right $ TyRecord fieldTypes

  -- Projection
  TmProj t label -> do
    ty <- typeOf ctx t
    case ty of
      TyRecord fields ->
        case Map.lookup label fields of
          Just fieldTy -> Right fieldTy
          Nothing -> Left $ FieldNotFound label ty
      TyBot -> Right TyBot  -- Projecting from Bot gives Bot
      _ -> Left $ NotARecord ty

  -- Ascription (explicit upcast)
  -- Γ ⊢ t : S    S <: T
  -- ────────────────────
  -- Γ ⊢ (t as T) : T
  TmAscribe t ty -> do
    actualTy <- typeOf ctx t
    if actualTy <: ty
      then Right ty
      else Left $ SubtypingError ty actualTy

-- =============================================================================
-- Join (Least Upper Bound)
-- =============================================================================

-- | Compute the join (least upper bound) of two types
-- This is used for if-then-else branches
join :: Type -> Type -> Maybe Type
join t1 t2
  -- If one is subtype of the other, take the supertype
  | t1 <: t2 = Just t2
  | t2 <: t1 = Just t1
  -- Bot is identity for join
  | TyBot <- t1 = Just t2
  | TyBot <- t2 = Just t1
  -- Top absorbs everything
  | TyTop <- t1 = Just TyTop
  | TyTop <- t2 = Just TyTop
  -- Functions: contravariant in argument (meet), covariant in result (join)
  | TyArr s1 s2 <- t1
  , TyArr u1 u2 <- t2
  = do
    argTy <- meet s1 u1  -- Meet for contravariant position
    resTy <- join s2 u2  -- Join for covariant position
    Just $ TyArr argTy resTy
  -- Records: intersection of fields with join of common field types
  | TyRecord fields1 <- t1
  , TyRecord fields2 <- t2
  = joinRecords fields1 fields2
  -- Otherwise, only Top works
  | otherwise = Just TyTop

-- | Join two record types (intersection of fields with join of types)
joinRecords :: Map Label Type -> Map Label Type -> Maybe Type
joinRecords fields1 fields2 = do
  let commonLabels = Map.keysSet fields1 `Set.intersection` Map.keysSet fields2
  joinedFields <- sequence $ Map.fromSet joinField commonLabels
  Just $ TyRecord joinedFields
  where
    joinField l = do
      ty1 <- Map.lookup l fields1
      ty2 <- Map.lookup l fields2
      join ty1 ty2

-- | Compute the meet (greatest lower bound) of two types
meet :: Type -> Type -> Maybe Type
meet t1 t2
  -- If one is subtype of the other, take the subtype
  | t1 <: t2 = Just t1
  | t2 <: t1 = Just t2
  -- Top is identity for meet
  | TyTop <- t1 = Just t2
  | TyTop <- t2 = Just t1
  -- Bot absorbs everything
  | TyBot <- t1 = Just TyBot
  | TyBot <- t2 = Just TyBot
  -- Functions
  | TyArr s1 s2 <- t1
  , TyArr u1 u2 <- t2
  = do
    argTy <- join s1 u1  -- Join for contravariant position
    resTy <- meet s2 u2  -- Meet for covariant position
    Just $ TyArr argTy resTy
  -- Records: union of fields with meet of common field types
  | TyRecord fields1 <- t1
  , TyRecord fields2 <- t2
  = meetRecords fields1 fields2
  -- Otherwise, only Bot works
  | otherwise = Just TyBot

-- | Meet two record types (union of fields with meet of common types)
meetRecords :: Map Label Type -> Map Label Type -> Maybe Type
meetRecords fields1 fields2 = do
  let allFields = Map.union fields1 fields2
  let commonLabels = Map.keysSet fields1 `Set.intersection` Map.keysSet fields2
  metFields <- myFoldM meetField allFields (Set.toList commonLabels)
  Just $ TyRecord metFields
  where
    meetField acc l = do
      ty1 <- Map.lookup l fields1
      ty2 <- Map.lookup l fields2
      metTy <- meet ty1 ty2
      Just $ Map.insert l metTy acc

-- Helper for foldM (avoiding Control.Monad import)
myFoldM :: Monad m => (b -> a -> m b) -> b -> [a] -> m b
myFoldM _ z [] = return z
myFoldM f z (x:xs) = f z x >>= \z' -> myFoldM f z' xs

