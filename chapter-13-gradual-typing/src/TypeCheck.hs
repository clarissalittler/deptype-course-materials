{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( -- * Type checking
    typeCheck
  , infer
  , checkType
    -- * Consistency
  , consistent
  , meet
  , join
    -- * Cast insertion
  , insertCasts
    -- * Errors
  , TypeError(..)
    -- * Context
  , Context
  , emptyContext
  ) where

import Syntax
import qualified Data.Map as Map
import Data.Map (Map)

-- =============================================================================
-- Type Errors
-- =============================================================================

data TypeError
  = UnboundVariable Var
  | TypeMismatch Type Type
  | Inconsistent Type Type
  | ExpectedFunction Type
  | CastError Type Type
  deriving (Eq, Show)

-- =============================================================================
-- Context
-- =============================================================================

-- | Type environment
type Context = Map Var Type

emptyContext :: Context
emptyContext = Map.empty

-- | Add a variable binding
bindVar :: Var -> Type -> Context -> Context
bindVar = Map.insert

-- | Look up a variable
lookupVar :: Var -> Context -> Maybe Type
lookupVar = Map.lookup

-- =============================================================================
-- Consistency
-- =============================================================================

-- | Check if two types are consistent (T₁ ~ T₂)
--
-- Consistency is the key relation in gradual typing.
-- Two types are consistent if one could be a plausible guess for the other.
--
-- Key rules:
--   ? ~ T        (dynamic is consistent with anything)
--   T ~ ?        (anything is consistent with dynamic)
--   B ~ B        (same base types are consistent)
--   T₁->T₂ ~ S₁->S₂  iff  T₁~S₁ and T₂~S₂
consistent :: Type -> Type -> Bool
consistent TyDyn _ = True
consistent _ TyDyn = True
consistent TyBool TyBool = True
consistent TyNat TyNat = True
consistent TyUnit TyUnit = True
consistent (TyFun t1 t2) (TyFun s1 s2) =
  consistent t1 s1 && consistent t2 s2
consistent _ _ = False

-- | Meet of two types (greatest lower bound with respect to precision)
--
-- The meet is the most precise type that is less precise than both.
-- This is used in type inference.
meet :: Type -> Type -> Maybe Type
meet TyDyn t = Just t
meet t TyDyn = Just t
meet TyBool TyBool = Just TyBool
meet TyNat TyNat = Just TyNat
meet TyUnit TyUnit = Just TyUnit
meet (TyFun t1 t2) (TyFun s1 s2) = do
  m1 <- meet t1 s1
  m2 <- meet t2 s2
  Just $ TyFun m1 m2
meet _ _ = Nothing

-- | Join of two types (least upper bound)
--
-- The join is the least precise type that is more precise than both.
join :: Type -> Type -> Maybe Type
join TyDyn _ = Just TyDyn
join _ TyDyn = Just TyDyn
join TyBool TyBool = Just TyBool
join TyNat TyNat = Just TyNat
join TyUnit TyUnit = Just TyUnit
join (TyFun t1 t2) (TyFun s1 s2) = do
  j1 <- join t1 s1
  j2 <- join t2 s2
  Just $ TyFun j1 j2
join _ _ = Nothing

-- =============================================================================
-- Type Checking
-- =============================================================================

-- | Type check a closed term
typeCheck :: Term -> Either TypeError Type
typeCheck = infer emptyContext

-- | Infer the type of a term
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
        if consistent tyArg ty2
          then Right tyRes
          else Left $ Inconsistent tyArg ty2
      TyDyn -> Right TyDyn  -- Dynamic function, result is dynamic
      _ -> Left $ ExpectedFunction ty1

  TmTrue -> Right TyBool
  TmFalse -> Right TyBool

  TmIf t1 t2 t3 -> do
    ty1 <- infer ctx t1
    if not (consistent ty1 TyBool)
      then Left $ Inconsistent ty1 TyBool
      else do
        ty2 <- infer ctx t2
        ty3 <- infer ctx t3
        case meet ty2 ty3 of
          Just ty -> Right ty
          Nothing ->
            case join ty2 ty3 of
              Just ty -> Right ty
              Nothing -> Left $ TypeMismatch ty2 ty3

  TmZero -> Right TyNat

  TmSucc t -> do
    ty <- infer ctx t
    if consistent ty TyNat
      then Right TyNat
      else Left $ Inconsistent ty TyNat

  TmPred t -> do
    ty <- infer ctx t
    if consistent ty TyNat
      then Right TyNat
      else Left $ Inconsistent ty TyNat

  TmIsZero t -> do
    ty <- infer ctx t
    if consistent ty TyNat
      then Right TyBool
      else Left $ Inconsistent ty TyNat

  TmUnit -> Right TyUnit

  TmLet x t1 t2 -> do
    ty1 <- infer ctx t1
    infer (bindVar x ty1 ctx) t2

  TmCast t tyFrom tyTo _ ->
    if consistent tyFrom tyTo
      then do
        tyActual <- infer ctx t
        if consistent tyActual tyFrom
          then Right tyTo
          else Left $ Inconsistent tyActual tyFrom
      else Left $ CastError tyFrom tyTo

  TmAscribe t ty -> do
    tyActual <- infer ctx t
    if consistent tyActual ty
      then Right ty
      else Left $ Inconsistent tyActual ty

  TmBlame ty _ -> Right ty

-- | Check a term against an expected type
checkType :: Context -> Term -> Type -> Either TypeError ()
checkType ctx t expectedTy = do
  actualTy <- infer ctx t
  if consistent actualTy expectedTy
    then Right ()
    else Left $ Inconsistent actualTy expectedTy

-- =============================================================================
-- Cast Insertion
-- =============================================================================

-- | Insert casts to make an implicitly-typed term explicit
--
-- This transforms a gradually-typed term into a cast calculus term
-- where all type conversions are explicit casts.
insertCasts :: Context -> Term -> Either TypeError Term
insertCasts ctx = \case
  Var x ->
    case lookupVar x ctx of
      Nothing -> Left $ UnboundVariable x
      Just _ -> Right $ Var x

  Lam x ty1 t -> do
    t' <- insertCasts (bindVar x ty1 ctx) t
    Right $ Lam x ty1 t'

  App t1 t2 -> do
    t1' <- insertCasts ctx t1
    t2' <- insertCasts ctx t2
    ty1 <- infer ctx t1
    ty2 <- infer ctx t2
    case ty1 of
      TyFun tyArg tyRes ->
        -- Insert cast from actual argument type to expected
        let t2'' = if tyArg == ty2 then t2' else TmCast t2' ty2 tyArg "arg"
        in Right $ App t1' t2''
      TyDyn ->
        -- Cast function to ? -> ?
        let t1'' = TmCast t1' TyDyn (TyFun TyDyn TyDyn) "fun"
            t2'' = TmCast t2' ty2 TyDyn "arg"
        in Right $ App t1'' t2''
      _ -> Left $ ExpectedFunction ty1

  TmTrue -> Right TmTrue
  TmFalse -> Right TmFalse

  TmIf t1 t2 t3 -> do
    t1' <- insertCasts ctx t1
    t2' <- insertCasts ctx t2
    t3' <- insertCasts ctx t3
    ty1 <- infer ctx t1
    -- Cast condition to Bool if needed
    let t1'' = if ty1 == TyBool then t1' else TmCast t1' ty1 TyBool "cond"
    Right $ TmIf t1'' t2' t3'

  TmZero -> Right TmZero
  TmSucc t -> TmSucc <$> insertCasts ctx t
  TmPred t -> TmPred <$> insertCasts ctx t
  TmIsZero t -> TmIsZero <$> insertCasts ctx t
  TmUnit -> Right TmUnit

  TmLet x t1 t2 -> do
    t1' <- insertCasts ctx t1
    ty1 <- infer ctx t1
    t2' <- insertCasts (bindVar x ty1 ctx) t2
    Right $ TmLet x t1' t2'

  TmCast t ty1 ty2 l -> do
    t' <- insertCasts ctx t
    Right $ TmCast t' ty1 ty2 l

  TmAscribe t ty -> do
    t' <- insertCasts ctx t
    tyActual <- infer ctx t
    -- Insert cast from actual to ascribed type
    if tyActual == ty
      then Right t'
      else Right $ TmCast t' tyActual ty "ascribe"

  TmBlame ty l -> Right $ TmBlame ty l
