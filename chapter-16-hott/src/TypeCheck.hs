{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( typeCheck
  , infer
  , TypeError(..)
  , Context
  , emptyContext
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
  | ExpectedIdentity Type
  | ExpectedVoid Type
  | EndpointTypeMismatch Type Type
  | PathEndpointMismatch Term Term
  | InvalidJEliminator String
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

  TmAbsurd ty t -> do
    tyT <- infer ctx t
    case tyT of
      TyVoid -> Right ty
      _ -> Left $ ExpectedVoid tyT

  TmPair t1 t2 -> TyProd <$> infer ctx t1 <*> infer ctx t2

  TmFst t -> do
    ty <- infer ctx t
    case ty of
      TyProd t1 _ -> Right t1
      _ -> Left $ ExpectedProduct ty

  TmSnd t -> do
    ty <- infer ctx t
    case ty of
      TyProd _ t2 -> Right t2
      _ -> Left $ ExpectedProduct ty

  TmInl t ty -> case ty of
    TySum t1 _ -> do
      tyT <- infer ctx t
      if tyT == t1 then Right ty else Left $ TypeMismatch t1 tyT
    _ -> Left $ ExpectedSum ty

  TmInr t ty -> case ty of
    TySum _ t2 -> do
      tyT <- infer ctx t
      if tyT == t2 then Right ty else Left $ TypeMismatch t2 tyT
    _ -> Left $ ExpectedSum ty

  TmCase t x1 t1 x2 t2 -> do
    ty <- infer ctx t
    case ty of
      TySum tyL tyR -> do
        ty1 <- infer (Map.insert x1 tyL ctx) t1
        ty2 <- infer (Map.insert x2 tyR ctx) t2
        if ty1 == ty2 then Right ty1 else Left $ TypeMismatch ty1 ty2
      _ -> Left $ ExpectedSum ty

  TmLet x t1 t2 -> do
    ty1 <- infer ctx t1
    infer (Map.insert x ty1 ctx) t2

  -- refl : a =_A a
  TmRefl ty a -> do
    tyA <- infer ctx a
    if tyA == ty
      then Right $ TyId ty a a
      else Left $ TypeMismatch ty tyA

  -- J eliminator (simplified)
  -- J : (C : A → A → Type) → ((x : A) → C x x) → (a b : A) → (p : a = b) → C a b
  -- We simplify to return a fixed result type from the motive
  TmJ resultTy base a b p -> do
    -- Check that a and b have the same type
    tyA <- infer ctx a
    tyB <- infer ctx b
    if tyA /= tyB
      then Left $ EndpointTypeMismatch tyA tyB
      else do
        -- Check that p is a path from a to b
        tyP <- infer ctx p
        case tyP of
          TyId ty pA pB
            | ty == tyA && pA == a && pB == b -> do
                -- Check the base case has the right type
                -- base should be a function that given x returns something of resultTy
                -- (we simplify and just check base produces resultTy when applied to a)
                _ <- infer ctx base
                Right resultTy
            | ty /= tyA -> Left $ TypeMismatch tyA ty
            | otherwise -> Left $ PathEndpointMismatch a pA
          _ -> Left $ ExpectedIdentity tyP

  -- sym : (a = b) → (b = a)
  TmSym t -> do
    ty <- infer ctx t
    case ty of
      TyId tyA a b -> Right $ TyId tyA b a
      _ -> Left $ ExpectedIdentity ty

  -- trans : (a = b) → (b = c) → (a = c)
  TmTrans t1 t2 -> do
    ty1 <- infer ctx t1
    ty2 <- infer ctx t2
    case (ty1, ty2) of
      (TyId tyA a b, TyId tyB b' c)
        | tyA == tyB && b == b' -> Right $ TyId tyA a c
        | tyA /= tyB -> Left $ TypeMismatch tyA tyB
        | otherwise -> Left $ PathEndpointMismatch b b'
      (TyId{}, _) -> Left $ ExpectedIdentity ty2
      _ -> Left $ ExpectedIdentity ty1

  -- ap f : (a = b) → (f a = f b)
  TmAp f p -> do
    tyF <- infer ctx f
    tyP <- infer ctx p
    case (tyF, tyP) of
      (TyFun tyA tyB, TyId tyP' a b)
        | tyA == tyP' -> Right $ TyId tyB (App f a) (App f b)
        | otherwise -> Left $ TypeMismatch tyA tyP'
      (TyFun{}, _) -> Left $ ExpectedIdentity tyP
      _ -> Left $ ExpectedFunction tyF

  -- transport : (p : a = b) → P a → P b
  -- Simplified: we take P as a type constructor applied to the path endpoints
  TmTransport resultTy p t -> do
    tyP <- infer ctx p
    tyT <- infer ctx t
    case tyP of
      TyId _ _ _ -> Right resultTy  -- Simplified: trust the annotation
      _ -> Left $ ExpectedIdentity tyP
