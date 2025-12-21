{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( typeCheck, infer
  , unfoldType
  , TypeError(..)
  , Context, emptyContext
  ) where

import Syntax
import qualified Data.Map as Map
import Data.Map (Map)

data TypeError
  = UnboundVariable Var
  | TypeMismatch Type Type
  | ExpectedFunction Type
  | ExpectedProduct Type
  | ExpectedSum Type
  | ExpectedRecursive Type
  | NotRecursiveType Type
  deriving (Eq, Show)

type Context = Map Var Type

emptyContext :: Context
emptyContext = Map.empty

typeCheck :: Term -> Either TypeError Type
typeCheck = infer emptyContext

infer :: Context -> Term -> Either TypeError Type
infer ctx = \case
  Var x -> maybe (Left $ UnboundVariable x) Right (Map.lookup x ctx)

  Lam x ty t -> TyFun ty <$> infer (Map.insert x ty ctx) t

  App t1 t2 -> do
    ty1 <- infer ctx t1
    ty2 <- infer ctx t2
    case ty1 of
      TyFun tyA tyB | tyA == ty2 -> Right tyB
                    | otherwise -> Left $ TypeMismatch tyA ty2
      _ -> Left $ ExpectedFunction ty1

  TmTrue -> Right TyBool
  TmFalse -> Right TyBool
  TmIf t1 t2 t3 -> do
    ty1 <- infer ctx t1
    case ty1 of
      TyBool -> do
        ty2 <- infer ctx t2
        ty3 <- infer ctx t3
        if ty2 == ty3 then Right ty2 else Left $ TypeMismatch ty2 ty3
      _ -> Left $ TypeMismatch TyBool ty1

  TmZero -> Right TyNat
  TmSucc t -> do { ty <- infer ctx t; if ty == TyNat then Right TyNat else Left $ TypeMismatch TyNat ty }
  TmPred t -> do { ty <- infer ctx t; if ty == TyNat then Right TyNat else Left $ TypeMismatch TyNat ty }
  TmIsZero t -> do { ty <- infer ctx t; if ty == TyNat then Right TyBool else Left $ TypeMismatch TyNat ty }

  TmUnit -> Right TyUnit

  TmPair t1 t2 -> TyProd <$> infer ctx t1 <*> infer ctx t2
  TmFst t -> do { ty <- infer ctx t; case ty of TyProd t1 _ -> Right t1; _ -> Left $ ExpectedProduct ty }
  TmSnd t -> do { ty <- infer ctx t; case ty of TyProd _ t2 -> Right t2; _ -> Left $ ExpectedProduct ty }

  TmInl t ty -> case ty of
    TySum t1 _ -> do { tyT <- infer ctx t; if tyT == t1 then Right ty else Left $ TypeMismatch t1 tyT }
    _ -> Left $ ExpectedSum ty
  TmInr t ty -> case ty of
    TySum _ t2 -> do { tyT <- infer ctx t; if tyT == t2 then Right ty else Left $ TypeMismatch t2 tyT }
    _ -> Left $ ExpectedSum ty

  TmCase t x1 t1 x2 t2 -> do
    ty <- infer ctx t
    case ty of
      TySum tyL tyR -> do
        ty1 <- infer (Map.insert x1 tyL ctx) t1
        ty2 <- infer (Map.insert x2 tyR ctx) t2
        if ty1 == ty2 then Right ty1 else Left $ TypeMismatch ty1 ty2
      _ -> Left $ ExpectedSum ty

  TmLet x t1 t2 -> do { ty1 <- infer ctx t1; infer (Map.insert x ty1 ctx) t2 }

  -- Fold: t must have T[μα.T/α] and result is μα.T
  TmFold muTy@(TyMu v tyBody) t -> do
    tyT <- infer ctx t
    let expected = substTyVar v muTy tyBody
    if tyT == expected then Right muTy else Left $ TypeMismatch expected tyT
  TmFold ty _ -> Left $ NotRecursiveType ty

  -- Unfold: t must have μα.T and result is T[μα.T/α]
  TmUnfold muTy@(TyMu v tyBody) t -> do
    tyT <- infer ctx t
    if tyT == muTy then Right (substTyVar v muTy tyBody) else Left $ TypeMismatch muTy tyT
  TmUnfold ty _ -> Left $ NotRecursiveType ty

-- | Unfold a recursive type one step
unfoldType :: Type -> Type
unfoldType (TyMu v tyBody) = substTyVar v (TyMu v tyBody) tyBody
unfoldType ty = ty
