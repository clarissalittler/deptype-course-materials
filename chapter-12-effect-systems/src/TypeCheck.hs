{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( -- * Type checking
    typeCheck
  , infer
  , checkType
  , TypeAndEffect(..)
    -- * Effect operations
  , rowContains
  , rowUnion
  , rowRemove
    -- * Errors
  , TypeError(..)
    -- * Context
  , Context
  , emptyContext
  , EffectEnv
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
  | UnboundEffect EffectLabel
  | UnboundOperation EffectLabel String
  | TypeMismatch Type Type
  | EffectMismatch EffectRow EffectRow
  | ExpectedFunction Type
  | ExpectedEffectPoly Type
  | UnhandledEffect EffectLabel
  | HandlerTypeMismatch
  | InvalidHandler String
  deriving (Eq, Show)

-- =============================================================================
-- Context
-- =============================================================================

-- | Type environment: variable -> type
type TypeEnv = Map Var Type

-- | Effect environment: effect label -> operations
type EffectEnv = Map EffectLabel [Operation]

-- | Effect row variables in scope
type EffectVarEnv = Set Var

-- | Full context
data Context = Context
  { ctxTypes      :: TypeEnv
  , ctxEffects    :: EffectEnv
  , ctxEffectVars :: EffectVarEnv
  }

emptyContext :: Context
emptyContext = Context Map.empty defaultEffects Set.empty

-- | Default effects available
defaultEffects :: EffectEnv
defaultEffects = Map.fromList
  [ ("State", [ Operation "get" TyUnit TyNat
              , Operation "put" TyNat TyUnit
              ])
  , ("Exception", [ Operation "throw" TyUnit TyUnit
                  , Operation "catch" TyUnit TyUnit  -- simplified
                  ])
  , ("IO", [ Operation "print" TyNat TyUnit
           , Operation "read" TyUnit TyNat
           ])
  , ("Choice", [ Operation "choose" TyBool TyBool
               ])
  ]

-- | Add a variable binding
bindVar :: Var -> Type -> Context -> Context
bindVar x ty ctx = ctx { ctxTypes = Map.insert x ty (ctxTypes ctx) }

-- | Add an effect row variable
bindEffectVar :: Var -> Context -> Context
bindEffectVar v ctx = ctx { ctxEffectVars = Set.insert v (ctxEffectVars ctx) }

-- | Look up a variable
lookupVar :: Var -> Context -> Maybe Type
lookupVar x ctx = Map.lookup x (ctxTypes ctx)

-- | Look up an effect
lookupEffect :: EffectLabel -> Context -> Maybe [Operation]
lookupEffect eff ctx = Map.lookup eff (ctxEffects ctx)

-- | Look up an operation in an effect
lookupOperation :: EffectLabel -> String -> Context -> Maybe Operation
lookupOperation eff op ctx = do
  ops <- lookupEffect eff ctx
  find (\o -> opName o == op) ops
  where
    find _ [] = Nothing
    find p (x:xs) = if p x then Just x else find p xs

-- =============================================================================
-- Type Checking
-- =============================================================================

-- | Type and effect of a computation
data TypeAndEffect = TypeAndEffect Type EffectRow
  deriving (Eq, Show)

-- | Type check a closed term
typeCheck :: Term -> Either TypeError TypeAndEffect
typeCheck = infer emptyContext

-- | Infer the type and effect of a term
infer :: Context -> Term -> Either TypeError TypeAndEffect
infer ctx = \case
  Var x ->
    case lookupVar x ctx of
      Nothing -> Left $ UnboundVariable x
      Just ty -> Right $ TypeAndEffect ty EffEmpty

  Lam x ty1 t -> do
    TypeAndEffect ty2 eff <- infer (bindVar x ty1 ctx) t
    Right $ TypeAndEffect (TyFun ty1 ty2 eff) EffEmpty

  App t1 t2 -> do
    TypeAndEffect ty1 eff1 <- infer ctx t1
    case ty1 of
      TyFun tyArg tyRes effFun -> do
        TypeAndEffect ty2 eff2 <- infer ctx t2
        if tyArg `typeEq` ty2
          then Right $ TypeAndEffect tyRes (rowUnion eff1 (rowUnion eff2 effFun))
          else Left $ TypeMismatch tyArg ty2
      _ -> Left $ ExpectedFunction ty1

  TmTrue -> Right $ TypeAndEffect TyBool EffEmpty
  TmFalse -> Right $ TypeAndEffect TyBool EffEmpty

  TmIf t1 t2 t3 -> do
    TypeAndEffect ty1 eff1 <- infer ctx t1
    case ty1 of
      TyBool -> do
        TypeAndEffect ty2 eff2 <- infer ctx t2
        TypeAndEffect ty3 eff3 <- infer ctx t3
        if ty2 `typeEq` ty3
          then Right $ TypeAndEffect ty2 (rowUnion eff1 (rowUnion eff2 eff3))
          else Left $ TypeMismatch ty2 ty3
      _ -> Left $ TypeMismatch TyBool ty1

  TmZero -> Right $ TypeAndEffect TyNat EffEmpty
  TmSucc t -> inferNatOp ctx t
  TmPred t -> inferNatOp ctx t

  TmIsZero t -> do
    TypeAndEffect ty eff <- infer ctx t
    case ty of
      TyNat -> Right $ TypeAndEffect TyBool eff
      _ -> Left $ TypeMismatch TyNat ty

  TmUnit -> Right $ TypeAndEffect TyUnit EffEmpty

  TmLet x t1 t2 -> do
    TypeAndEffect ty1 eff1 <- infer ctx t1
    TypeAndEffect ty2 eff2 <- infer (bindVar x ty1 ctx) t2
    Right $ TypeAndEffect ty2 (rowUnion eff1 eff2)

  TmPerform eff op t -> do
    case lookupOperation eff op ctx of
      Nothing -> Left $ UnboundOperation eff op
      Just operation -> do
        TypeAndEffect tyArg effArg <- infer ctx t
        if opParam operation `typeEq` tyArg
          then Right $ TypeAndEffect (opReturn operation)
                                     (rowUnion effArg (EffLabel eff EffEmpty))
          else Left $ TypeMismatch (opParam operation) tyArg

  TmHandle t h -> do
    TypeAndEffect tyBody effBody <- infer ctx t
    -- Check that handler handles the effect
    let handledEff = handlerEffect h
    if not (rowContains handledEff effBody)
      then -- Effect not in body, handler has no effect
           Right $ TypeAndEffect tyBody effBody
      else do
        -- Type check the handler
        checkHandler ctx h tyBody
        -- Remove handled effect from result
        let effResult = rowRemove handledEff effBody
        Right $ TypeAndEffect tyBody effResult

  TmEffAbs v t -> do
    TypeAndEffect ty eff <- infer (bindEffectVar v ctx) t
    Right $ TypeAndEffect (TyForallEff v ty) eff

  TmEffApp t eff -> do
    TypeAndEffect ty effT <- infer ctx t
    case ty of
      TyForallEff v tyBody ->
        Right $ TypeAndEffect (substEffectRow v eff tyBody) effT
      _ -> Left $ ExpectedEffectPoly ty

  TmReturn t -> do
    TypeAndEffect ty eff <- infer ctx t
    Right $ TypeAndEffect ty eff

-- | Check a term against an expected type
checkType :: Context -> Term -> Type -> Either TypeError EffectRow
checkType ctx t expectedTy = do
  TypeAndEffect actualTy eff <- infer ctx t
  if actualTy `typeEq` expectedTy
    then Right eff
    else Left $ TypeMismatch expectedTy actualTy

-- | Infer type for nat operations
inferNatOp :: Context -> Term -> Either TypeError TypeAndEffect
inferNatOp ctx t = do
  TypeAndEffect ty eff <- infer ctx t
  case ty of
    TyNat -> Right $ TypeAndEffect TyNat eff
    _ -> Left $ TypeMismatch TyNat ty

-- | Type check a handler
checkHandler :: Context -> Handler -> Type -> Either TypeError ()
checkHandler ctx h bodyTy = do
  -- Check return clause: should transform result type
  let (retVar, retBody) = handlerReturn h
  let ctx' = bindVar retVar bodyTy ctx
  _ <- infer ctx' retBody
  -- Check operation clauses
  let eff = handlerEffect h
  case lookupEffect eff ctx of
    Nothing -> Left $ UnboundEffect eff
    Just ops -> do
      mapM_ (checkOpClause ctx h ops) (handlerOps h)
      Right ()

-- | Check an operation clause in a handler
checkOpClause :: Context -> Handler -> [Operation] -> (String, Var, Var, Term) -> Either TypeError ()
checkOpClause ctx _h ops (opName', paramVar, contVar, body) = do
  -- Find the operation
  case filter (\o -> opName o == opName') ops of
    [] -> Left $ InvalidHandler ("Unknown operation: " ++ opName')
    (op:_) -> do
      -- The continuation has type: opReturn -> result
      -- For now, we do a simplified check
      let ctx' = bindVar paramVar (opParam op) $
                 bindVar contVar (TyFun (opReturn op) TyUnit EffEmpty) ctx
      _ <- infer ctx' body
      Right ()

-- =============================================================================
-- Effect Row Operations
-- =============================================================================

-- | Check if an effect label is in a row
rowContains :: EffectLabel -> EffectRow -> Bool
rowContains _ EffEmpty = False
rowContains eff (EffLabel l r)
  | eff == l = True
  | otherwise = rowContains eff r
rowContains _ (EffVar _) = True  -- Conservative: variable might contain it

-- | Union of two effect rows
rowUnion :: EffectRow -> EffectRow -> EffectRow
rowUnion EffEmpty r = r
rowUnion r EffEmpty = r
rowUnion (EffLabel l r1) r2
  | rowContains l r2 = rowUnion r1 r2
  | otherwise = EffLabel l (rowUnion r1 r2)
rowUnion (EffVar v) r = addRowVar v r
  where
    addRowVar v' EffEmpty = EffVar v'
    addRowVar v' (EffLabel l r') = EffLabel l (addRowVar v' r')
    addRowVar v' r'@(EffVar _) = if v' == extractVar r' then r' else EffVar v'
    extractVar (EffVar x) = x
    extractVar _ = ""

-- | Remove an effect from a row
rowRemove :: EffectLabel -> EffectRow -> EffectRow
rowRemove _ EffEmpty = EffEmpty
rowRemove eff (EffLabel l r)
  | eff == l = rowRemove eff r
  | otherwise = EffLabel l (rowRemove eff r)
rowRemove _ r@(EffVar _) = r  -- Can't remove from variable

-- | Check if one row is a subset of another
rowSubset :: EffectRow -> EffectRow -> Bool
rowSubset EffEmpty _ = True
rowSubset (EffLabel l r) r2 = rowContains l r2 && rowSubset r r2
rowSubset (EffVar _) (EffVar _) = True  -- Variables match
rowSubset (EffVar _) _ = False

-- | Get all effect labels in a row
rowLabels :: EffectRow -> Set EffectLabel
rowLabels EffEmpty = Set.empty
rowLabels (EffLabel l r) = Set.insert l (rowLabels r)
rowLabels (EffVar _) = Set.empty

-- =============================================================================
-- Type Equality
-- =============================================================================

-- | Check type equality
typeEq :: Type -> Type -> Bool
typeEq TyUnit TyUnit = True
typeEq TyBool TyBool = True
typeEq TyNat TyNat = True
typeEq (TyFun t1 t2 e1) (TyFun t1' t2' e2) =
  typeEq t1 t1' && typeEq t2 t2' && effEq e1 e2
typeEq (TyForallEff v1 t1) (TyForallEff v2 t2) =
  -- Alpha equivalence
  typeEq t1 (substEffectRow v2 (EffVar v1) t2)
typeEq _ _ = False

-- | Check effect row equality
effEq :: EffectRow -> EffectRow -> Bool
effEq EffEmpty EffEmpty = True
effEq (EffVar v1) (EffVar v2) = v1 == v2
effEq r1 r2 = rowLabels r1 == rowLabels r2 &&
              rowSubset r1 r2 && rowSubset r2 r1

-- =============================================================================
-- Substitution
-- =============================================================================

-- | Substitute an effect row for an effect variable in a type
substEffectRow :: Var -> EffectRow -> Type -> Type
substEffectRow _ _ TyUnit = TyUnit
substEffectRow _ _ TyBool = TyBool
substEffectRow _ _ TyNat = TyNat
substEffectRow v eff (TyFun t1 t2 e) =
  TyFun (substEffectRow v eff t1)
        (substEffectRow v eff t2)
        (substRowInRow v eff e)
substEffectRow v eff (TyForallEff v' t)
  | v == v' = TyForallEff v' t  -- Shadowed
  | otherwise = TyForallEff v' (substEffectRow v eff t)

-- | Substitute an effect row for a variable in another row
substRowInRow :: Var -> EffectRow -> EffectRow -> EffectRow
substRowInRow _ _ EffEmpty = EffEmpty
substRowInRow v eff (EffLabel l r) = EffLabel l (substRowInRow v eff r)
substRowInRow v eff (EffVar v')
  | v == v' = eff
  | otherwise = EffVar v'
