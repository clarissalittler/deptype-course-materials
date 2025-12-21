{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( -- * Type checking
    typeCheck
  , infer
    -- * Row operations
  , rowHas
  , rowGet
  , rowExtend
  , rowRestrict
    -- * Errors
  , TypeError(..)
    -- * Context
  , Context
  , emptyContext
  ) where

import Syntax
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

-- =============================================================================
-- Type Errors
-- =============================================================================

data TypeError
  = UnboundVariable Var
  | UnboundRowVar RowVar
  | TypeMismatch Type Type
  | ExpectedFunction Type
  | ExpectedRecord Type
  | ExpectedVariant Type
  | MissingLabel Label
  | DuplicateLabel Label
  | RowMismatch Row Row
  deriving (Eq, Show)

-- =============================================================================
-- Context
-- =============================================================================

-- | Type environment
type TypeEnv = Map Var Type

-- | Row variables in scope
type RowVarEnv = Set RowVar

data Context = Context
  { ctxTypes   :: TypeEnv
  , ctxRowVars :: RowVarEnv
  }

emptyContext :: Context
emptyContext = Context Map.empty Set.empty

bindVar :: Var -> Type -> Context -> Context
bindVar x ty ctx = ctx { ctxTypes = Map.insert x ty (ctxTypes ctx) }

bindRowVar :: RowVar -> Context -> Context
bindRowVar v ctx = ctx { ctxRowVars = Set.insert v (ctxRowVars ctx) }

lookupVar :: Var -> Context -> Maybe Type
lookupVar x ctx = Map.lookup x (ctxTypes ctx)

-- =============================================================================
-- Type Checking
-- =============================================================================

typeCheck :: Term -> Either TypeError Type
typeCheck = infer emptyContext

infer :: Context -> Term -> Either TypeError Type
infer ctx = \case
  Var x ->
    case lookupVar x ctx of
      Nothing -> Left $ UnboundVariable x
      Just ty -> Right ty

  Lam x ty1 t -> do
    ty2 <- infer (bindVar x ty1 ctx) t
    Right $ TyFun ty1 ty2

  App t1 t2 -> do
    ty1 <- infer ctx t1
    ty2 <- infer ctx t2
    case ty1 of
      TyFun tyArg tyRes ->
        if tyArg == ty2
          then Right tyRes
          else Left $ TypeMismatch tyArg ty2
      _ -> Left $ ExpectedFunction ty1

  TmTrue -> Right TyBool
  TmFalse -> Right TyBool

  TmIf t1 t2 t3 -> do
    ty1 <- infer ctx t1
    case ty1 of
      TyBool -> do
        ty2 <- infer ctx t2
        ty3 <- infer ctx t3
        if ty2 == ty3
          then Right ty2
          else Left $ TypeMismatch ty2 ty3
      _ -> Left $ TypeMismatch TyBool ty1

  TmZero -> Right TyNat
  TmSucc t -> do
    ty <- infer ctx t
    if ty == TyNat then Right TyNat else Left $ TypeMismatch TyNat ty
  TmPred t -> do
    ty <- infer ctx t
    if ty == TyNat then Right TyNat else Left $ TypeMismatch TyNat ty
  TmIsZero t -> do
    ty <- infer ctx t
    if ty == TyNat then Right TyBool else Left $ TypeMismatch TyNat ty

  TmUnit -> Right TyUnit

  TmRecord fields -> do
    fieldTypes <- mapM (infer ctx) fields
    Right $ TyRecord (mapToRow fieldTypes)

  TmProj t l -> do
    ty <- infer ctx t
    case ty of
      TyRecord row ->
        case rowGet l row of
          Just fieldTy -> Right fieldTy
          Nothing -> Left $ MissingLabel l
      _ -> Left $ ExpectedRecord ty

  TmExtend t1 l t2 -> do
    ty1 <- infer ctx t1
    ty2 <- infer ctx t2
    case ty1 of
      TyRecord row ->
        if rowHas l row
          then Left $ DuplicateLabel l
          else Right $ TyRecord (RowExtend l ty2 row)
      _ -> Left $ ExpectedRecord ty1

  TmRestrict t l -> do
    ty <- infer ctx t
    case ty of
      TyRecord row ->
        case rowRestrict l row of
          Just row' -> Right $ TyRecord row'
          Nothing -> Left $ MissingLabel l
      _ -> Left $ ExpectedRecord ty

  TmVariant l t ty -> do
    tyActual <- infer ctx t
    case ty of
      TyVariant row ->
        case rowGet l row of
          Just expectedTy ->
            if tyActual == expectedTy
              then Right ty
              else Left $ TypeMismatch expectedTy tyActual
          Nothing -> Left $ MissingLabel l
      _ -> Left $ ExpectedVariant ty

  TmCase t cases -> do
    ty <- infer ctx t
    case ty of
      TyVariant row -> do
        -- Type check each case
        resultTys <- mapM (checkCase ctx row) cases
        -- All results must have same type
        case resultTys of
          [] -> Left $ ExpectedVariant ty
          (firstTy:restTys) ->
            if all (== firstTy) restTys
              then Right firstTy
              else Left $ TypeMismatch firstTy (head $ filter (/= firstTy) restTys)
      _ -> Left $ ExpectedVariant ty

  TmLet x t1 t2 -> do
    ty1 <- infer ctx t1
    infer (bindVar x ty1 ctx) t2

  TmRowAbs v t -> do
    ty <- infer (bindRowVar v ctx) t
    Right $ TyForallRow v ty

  TmRowApp t r -> do
    ty <- infer ctx t
    case ty of
      TyForallRow v tyBody -> Right $ substRow v r tyBody
      _ -> Left $ ExpectedFunction ty  -- Reusing error for simplicity

-- | Check a case branch
checkCase :: Context -> Row -> (Label, Var, Term) -> Either TypeError Type
checkCase ctx row (l, x, body) =
  case rowGet l row of
    Just ty -> infer (bindVar x ty ctx) body
    Nothing -> Left $ MissingLabel l

-- =============================================================================
-- Row Operations
-- =============================================================================

-- | Check if row contains a label
rowHas :: Label -> Row -> Bool
rowHas _ RowEmpty = False
rowHas l (RowExtend l' _ r)
  | l == l' = True
  | otherwise = rowHas l r
rowHas _ (RowVar _) = False

-- | Get type of label in row
rowGet :: Label -> Row -> Maybe Type
rowGet _ RowEmpty = Nothing
rowGet l (RowExtend l' ty r)
  | l == l' = Just ty
  | otherwise = rowGet l r
rowGet _ (RowVar _) = Nothing

-- | Extend a row with a new label
rowExtend :: Label -> Type -> Row -> Row
rowExtend = RowExtend

-- | Remove a label from a row
rowRestrict :: Label -> Row -> Maybe Row
rowRestrict _ RowEmpty = Nothing
rowRestrict l (RowExtend l' ty r)
  | l == l' = Just r
  | otherwise = RowExtend l' ty <$> rowRestrict l r
rowRestrict _ (RowVar _) = Nothing

-- | Convert a map to a row
mapToRow :: Map Label Type -> Row
mapToRow = Map.foldrWithKey RowExtend RowEmpty

-- | Substitute a row for a row variable in a type
substRow :: RowVar -> Row -> Type -> Type
substRow _ _ TyBool = TyBool
substRow _ _ TyNat = TyNat
substRow _ _ TyUnit = TyUnit
substRow v r (TyFun t1 t2) = TyFun (substRow v r t1) (substRow v r t2)
substRow v r (TyRecord row) = TyRecord (substRowInRow v r row)
substRow v r (TyVariant row) = TyVariant (substRowInRow v r row)
substRow v r (TyForallRow v' t)
  | v == v' = TyForallRow v' t
  | otherwise = TyForallRow v' (substRow v r t)

-- | Substitute a row for a row variable in another row
substRowInRow :: RowVar -> Row -> Row -> Row
substRowInRow _ _ RowEmpty = RowEmpty
substRowInRow v r (RowExtend l ty row) =
  RowExtend l (substRow v r ty) (substRowInRow v r row)
substRowInRow v r (RowVar v')
  | v == v' = r
  | otherwise = RowVar v'
