{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( TypeError(..)
  , TypeContext
  , typeOf
  , typeCheck
  , emptyContext
  , extendContext
  , typeOfPattern
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Monad (unless, when)
import Data.List (nub)

-- | Type checking context
type TypeContext = Map Var Type

-- | Empty context
emptyContext :: TypeContext
emptyContext = Map.empty

-- | Extend context
extendContext :: Var -> Type -> TypeContext -> TypeContext
extendContext = Map.insert

-- | Type errors
data TypeError
  = UnboundVariable Var
  | TypeMismatch { tmExpected :: Type, tmActual :: Type }
  | NotAFunction Type
  | ConditionNotBool Type
  | ArgumentTypeMismatch { paramTy :: Type, argTy :: Type }
  | NotANat Type
  | NotAProduct Type
  | NotASum Type
  | NotARecord Type
  | NotAList Type
  | FieldNotFound Label
  | VariantLabelNotFound Label
  | PatternTypeMismatch Pattern Type
  | NonExhaustivePatterns
  | DuplicateLabel Label
  | DuplicatePatternVar Var
  deriving (Eq, Show)

-- | Type check a term
typeOf :: TypeContext -> Term -> Either TypeError Type
typeOf ctx = \case
  -- T-Var
  Var x ->
    case Map.lookup x ctx of
      Just ty -> Right ty
      Nothing -> Left (UnboundVariable x)

  -- T-Abs
  Lam x ty t -> do
    let ctx' = extendContext x ty ctx
    tyBody <- typeOf ctx' t
    return $ TyArr ty tyBody

  -- T-App
  App t1 t2 -> do
    ty1 <- typeOf ctx t1
    ty2 <- typeOf ctx t2
    case ty1 of
      TyArr tyParam tyResult -> do
        unless (tyParam == ty2) $
          Left (ArgumentTypeMismatch tyParam ty2)
        return tyResult
      _ -> Left (NotAFunction ty1)

  -- Booleans
  TmTrue -> Right TyBool
  TmFalse -> Right TyBool
  TmIf t1 t2 t3 -> do
    ty1 <- typeOf ctx t1
    unless (ty1 == TyBool) $ Left (ConditionNotBool ty1)
    ty2 <- typeOf ctx t2
    ty3 <- typeOf ctx t3
    unless (ty2 == ty3) $ Left (TypeMismatch ty2 ty3)
    return ty2

  -- Natural numbers
  TmZero -> Right TyNat
  TmSucc t -> do
    ty <- typeOf ctx t
    unless (ty == TyNat) $ Left (NotANat ty)
    return TyNat
  TmPred t -> do
    ty <- typeOf ctx t
    unless (ty == TyNat) $ Left (NotANat ty)
    return TyNat
  TmIsZero t -> do
    ty <- typeOf ctx t
    unless (ty == TyNat) $ Left (NotANat ty)
    return TyBool

  -- Unit
  TmUnit -> Right TyUnit

  -- Products (pairs)
  TmPair t1 t2 -> do
    ty1 <- typeOf ctx t1
    ty2 <- typeOf ctx t2
    return $ TyProd ty1 ty2

  TmFst t -> do
    ty <- typeOf ctx t
    case ty of
      TyProd ty1 _ -> return ty1
      _ -> Left (NotAProduct ty)

  TmSnd t -> do
    ty <- typeOf ctx t
    case ty of
      TyProd _ ty2 -> return ty2
      _ -> Left (NotAProduct ty)

  -- Sums
  TmInl tyRight t -> do
    tyLeft <- typeOf ctx t
    return $ TySum tyLeft tyRight

  TmInr tyLeft t -> do
    tyRight <- typeOf ctx t
    return $ TySum tyLeft tyRight

  TmCase t x1 t1 x2 t2 -> do
    ty <- typeOf ctx t
    case ty of
      TySum tyLeft tyRight -> do
        let ctx1 = extendContext x1 tyLeft ctx
        let ctx2 = extendContext x2 tyRight ctx
        ty1 <- typeOf ctx1 t1
        ty2 <- typeOf ctx2 t2
        unless (ty1 == ty2) $ Left (TypeMismatch ty1 ty2)
        return ty1
      _ -> Left (NotASum ty)

  -- Records
  TmRecord fields -> do
    -- Check for duplicate labels
    let labels = Map.keys fields
    when (length labels /= length (nub labels)) $
      Left (DuplicateLabel (head $ labels \\ nub labels))
    -- Type check each field
    fieldTypes <- traverse (typeOf ctx) fields
    return $ TyRecord fieldTypes

  TmProj t label -> do
    ty <- typeOf ctx t
    case ty of
      TyRecord fields ->
        case Map.lookup label fields of
          Just fieldTy -> return fieldTy
          Nothing -> Left (FieldNotFound label)
      _ -> Left (NotARecord ty)

  -- Variants
  TmTag label t variantTy -> do
    ty <- typeOf ctx t
    case variantTy of
      TyVariant fields ->
        case Map.lookup label fields of
          Just expectedTy ->
            if ty == expectedTy
              then return variantTy
              else Left (TypeMismatch expectedTy ty)
          Nothing -> Left (VariantLabelNotFound label)
      _ -> Left (NotARecord variantTy)

  TmCaseVariant t cases -> do
    ty <- typeOf ctx t
    case ty of
      TyVariant variantFields -> do
        -- Check each case
        caseTys <- mapM checkCase cases
        -- Ensure all cases return the same type
        case caseTys of
          [] -> Left NonExhaustivePatterns
          (ty1:tys) -> do
            unless (all (== ty1) tys) $
              Left (TypeMismatch ty1 (head $ filter (/= ty1) tys))
            return ty1
        where
          checkCase (label, x, ti) =
            case Map.lookup label variantFields of
              Just fieldTy -> do
                let ctx' = extendContext x fieldTy ctx
                typeOf ctx' ti
              Nothing -> Left (VariantLabelNotFound label)
      _ -> Left (NotARecord ty)

  -- Lists
  TmNil ty -> Right (TyList ty)

  TmCons t ts -> do
    ty <- typeOf ctx t
    tyList <- typeOf ctx ts
    case tyList of
      TyList elemTy ->
        if ty == elemTy
          then return tyList
          else Left (TypeMismatch elemTy ty)
      _ -> Left (NotAList tyList)

  TmIsNil t -> do
    ty <- typeOf ctx t
    case ty of
      TyList _ -> return TyBool
      _ -> Left (NotAList ty)

  TmHead t -> do
    ty <- typeOf ctx t
    case ty of
      TyList elemTy -> return elemTy
      _ -> Left (NotAList ty)

  TmTail t -> do
    ty <- typeOf ctx t
    case ty of
      TyList _ -> return ty
      _ -> Left (NotAList ty)

  -- Pattern matching
  TmMatch t cases -> do
    scrutineeTy <- typeOf ctx t
    -- Type check each case
    caseTys <- mapM (checkPatternCase scrutineeTy) cases
    case caseTys of
      [] -> Left NonExhaustivePatterns
      (ty1:tys) -> do
        unless (all (== ty1) tys) $
          Left (TypeMismatch ty1 (head $ filter (/= ty1) tys))
        return ty1
    where
      checkPatternCase :: Type -> (Pattern, Term) -> Either TypeError Type
      checkPatternCase scrutTy (pat, body) = do
        patCtx <- typeOfPattern pat scrutTy
        -- Check for duplicate pattern variables
        let patVars = Map.keys patCtx
        when (length patVars /= length (nub patVars)) $
          Left (DuplicatePatternVar (head $ patVars \\ nub patVars))
        -- Type check body with pattern bindings
        let ctx' = Map.union patCtx ctx
        typeOf ctx' body

-- | Get type bindings from a pattern
typeOfPattern :: Pattern -> Type -> Either TypeError TypeContext
typeOfPattern pat ty = case (pat, ty) of
  (PatVar x, _) -> Right (Map.singleton x ty)
  (PatWild, _) -> Right Map.empty
  (PatUnit, TyUnit) -> Right Map.empty
  (PatUnit, _) -> Left (PatternTypeMismatch pat ty)
  (PatTrue, TyBool) -> Right Map.empty
  (PatTrue, _) -> Left (PatternTypeMismatch pat ty)
  (PatFalse, TyBool) -> Right Map.empty
  (PatFalse, _) -> Left (PatternTypeMismatch pat ty)
  (PatZero, TyNat) -> Right Map.empty
  (PatZero, _) -> Left (PatternTypeMismatch pat ty)
  (PatSucc p, TyNat) -> typeOfPattern p TyNat
  (PatSucc _, _) -> Left (PatternTypeMismatch pat ty)
  (PatPair p1 p2, TyProd ty1 ty2) -> do
    ctx1 <- typeOfPattern p1 ty1
    ctx2 <- typeOfPattern p2 ty2
    Right (Map.union ctx1 ctx2)
  (PatPair _ _, _) -> Left (PatternTypeMismatch pat ty)
  (PatInl p, TySum ty1 _) -> typeOfPattern p ty1
  (PatInl _, _) -> Left (PatternTypeMismatch pat ty)
  (PatInr p, TySum _ ty2) -> typeOfPattern p ty2
  (PatInr _, _) -> Left (PatternTypeMismatch pat ty)
  (PatVariant label p, TyVariant fields) ->
    case Map.lookup label fields of
      Just fieldTy -> typeOfPattern p fieldTy
      Nothing -> Left (VariantLabelNotFound label)
  (PatVariant _ _, _) -> Left (PatternTypeMismatch pat ty)
  (PatNil, TyList _) -> Right Map.empty
  (PatNil, _) -> Left (PatternTypeMismatch pat ty)
  (PatCons p ps, TyList elemTy) -> do
    ctx1 <- typeOfPattern p elemTy
    ctx2 <- typeOfPattern ps (TyList elemTy)
    Right (Map.union ctx1 ctx2)
  (PatCons _ _, _) -> Left (PatternTypeMismatch pat ty)

-- | Type check a closed term
typeCheck :: Term -> Either TypeError Type
typeCheck = typeOf emptyContext

-- | List difference (\\)
(\\) :: Eq a => [a] -> [a] -> [a]
xs \\ ys = filter (`notElem` ys) xs
