{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( Context
  , TypeError(..)
  , typeOf
  , typeCheck
  , emptyCtx
  , extendCtx
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- | Type context: maps variables to their types
type Context = Map Name Term

-- | Empty context
emptyCtx :: Context
emptyCtx = Map.empty

-- | Extend context with a new binding
extendCtx :: Name -> Term -> Context -> Context
extendCtx = Map.insert

-- | Type checking errors
data TypeError
  = UnboundVariable Name
  | TypeMismatch Term Term  -- expected, actual
  | NotAPi Term
  | NotASigma Term
  | NotAType Term
  | CannotInfer Term
  | NotSupported String
  deriving (Eq, Show)

-- | Definitional equality (normalize + alpha equivalence)
typeEq :: Term -> Term -> Bool
typeEq t1 t2 = alphaEq (normalize t1) (normalize t2)

-- | Fully normalize a term (beta-reduction under binders)
normalize :: Term -> Term
normalize = \case
  Universe l -> Universe l
  Var x -> Var x
  Lam x ty t -> Lam x (normalize ty) (normalize t)
  App t1 t2 ->
    let t1' = normalize t1
        t2' = normalize t2
    in case t1' of
        Lam x _ body -> normalize (subst x t2' body)
        _ -> App t1' t2'
  Pi x a b -> Pi x (normalize a) (normalize b)
  Sigma x a b -> Sigma x (normalize a) (normalize b)
  Pair t1 t2 -> Pair (normalize t1) (normalize t2)
  Fst t ->
    case normalize t of
      Pair v1 _ -> v1
      t' -> Fst t'
  Snd t ->
    case normalize t of
      Pair _ v2 -> v2
      t' -> Snd t'
  Ind name -> Ind name
  Con name ts -> Con name (map normalize ts)
  Match t branches -> Match (normalize t) [(p, normalize rhs) | (p, rhs) <- branches]
  Eq a x y -> Eq (normalize a) (normalize x) (normalize y)
  Refl t -> Refl (normalize t)
  J a c p x y eq ->
    let a' = normalize a
        c' = normalize c
        p' = normalize p
        x' = normalize x
        y' = normalize y
        eq' = normalize eq
    in case eq' of
        Refl z | alphaEq x' y' && alphaEq y' z -> normalize p'
        _ -> J a' c' p' x' y' eq'
  Nat -> Nat
  Zero -> Zero
  Succ t -> Succ (normalize t)
  NatElim p z s n ->
    let p' = normalize p
        z' = normalize z
        s' = normalize s
        n' = normalize n
    in case n' of
        Zero -> z'
        Succ k -> normalize (App (App s' k) (NatElim p' z' s' k))
        _ -> NatElim p' z' s' n'
  Bool -> Bool
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  BoolElim p t f b ->
    let p' = normalize p
        t' = normalize t
        f' = normalize f
        b' = normalize b
    in case b' of
        TmTrue -> t'
        TmFalse -> f'
        _ -> BoolElim p' t' f' b'
  Unit -> Unit
  TT -> TT
  UnitElim p u x ->
    let p' = normalize p
        u' = normalize u
        x' = normalize x
    in case x' of
        TT -> u'
        _ -> UnitElim p' u' x'
  Empty -> Empty
  EmptyElim p e -> EmptyElim (normalize p) (normalize e)

-- | Infer the type of a term
typeOf :: Context -> Term -> Either TypeError Term
typeOf = infer

-- | Check that a term has a given type
typeCheck :: Context -> Term -> Term -> Either TypeError ()
typeCheck = check

infer :: Context -> Term -> Either TypeError Term
infer ctx = \case
  Universe i -> Right (Universe (i + 1))
  Var x -> case Map.lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left (UnboundVariable x)
  Pi x a b -> do
    aType <- infer ctx a
    bType <- infer (extendCtx x a ctx) b
    case (normalize aType, normalize bType) of
      (Universe i, Universe j) -> Right (Universe (max i j))
      (Universe _, _) -> Left (NotAType b)
      _ -> Left (NotAType a)
  Sigma x a b -> do
    aType <- infer ctx a
    bType <- infer (extendCtx x a ctx) b
    case (normalize aType, normalize bType) of
      (Universe i, Universe j) -> Right (Universe (max i j))
      (Universe _, _) -> Left (NotAType b)
      _ -> Left (NotAType a)
  Lam x ty t -> do
    checkType ctx ty
    tyBody <- infer (extendCtx x ty ctx) t
    Right (Pi x ty tyBody)
  App t1 t2 -> do
    ty1 <- infer ctx t1
    case normalize ty1 of
      Pi x a b -> do
        check ctx t2 a
        Right (subst x t2 b)
      _ -> Left (NotAPi ty1)
  Pair t1 t2 -> Left (CannotInfer (Pair t1 t2))
  Fst t -> do
    ty <- infer ctx t
    case normalize ty of
      Sigma _ a _ -> Right a
      _ -> Left (NotASigma ty)
  Snd t -> do
    ty <- infer ctx t
    case normalize ty of
      Sigma x _ b -> Right (subst x (Fst t) b)
      _ -> Left (NotASigma ty)
  Nat -> Right (Universe 0)
  Zero -> Right Nat
  Succ t -> do
    check ctx t Nat
    Right Nat
  NatElim p z s n -> do
    pTy <- infer ctx p
    case normalize pTy of
      Pi _ a pBodyTy -> do
        if typeEq a Nat
          then case normalize pBodyTy of
            Universe _ -> do
              check ctx z (App p Zero)
              let stepTy =
                    Pi "k" Nat
                      (Pi "rec" (App p (Var "k"))
                        (App p (Succ (Var "k"))))
              check ctx s stepTy
              check ctx n Nat
              Right (App p n)
            _ -> Left (NotAType p)
          else Left (TypeMismatch Nat a)
      _ -> Left (NotAPi pTy)
  Bool -> Right (Universe 0)
  TmTrue -> Right Bool
  TmFalse -> Right Bool
  BoolElim p t f b -> do
    pTy <- infer ctx p
    case normalize pTy of
      Pi _ a pBodyTy -> do
        if typeEq a Bool
          then case normalize pBodyTy of
            Universe _ -> do
              check ctx t (App p TmTrue)
              check ctx f (App p TmFalse)
              check ctx b Bool
              Right (App p b)
            _ -> Left (NotAType p)
          else Left (TypeMismatch Bool a)
      _ -> Left (NotAPi pTy)
  Unit -> Right (Universe 0)
  TT -> Right Unit
  UnitElim p u x -> do
    pTy <- infer ctx p
    case normalize pTy of
      Pi _ a pBodyTy -> do
        if typeEq a Unit
          then case normalize pBodyTy of
            Universe _ -> do
              check ctx u (App p TT)
              check ctx x Unit
              Right (App p x)
            _ -> Left (NotAType p)
          else Left (TypeMismatch Unit a)
      _ -> Left (NotAPi pTy)
  Empty -> Right (Universe 0)
  EmptyElim p e -> do
    pTy <- infer ctx p
    case normalize pTy of
      Pi _ a pBodyTy -> do
        if typeEq a Empty
          then case normalize pBodyTy of
            Universe _ -> do
              check ctx e Empty
              Right (App p e)
            _ -> Left (NotAType p)
          else Left (TypeMismatch Empty a)
      _ -> Left (NotAPi pTy)
  Eq a x y -> do
    aTy <- infer ctx a
    case normalize aTy of
      Universe i -> do
        check ctx x a
        check ctx y a
        Right (Universe i)
      _ -> Left (NotAType a)
  Refl t -> do
    ty <- infer ctx t
    Right (Eq ty t t)
  J a c p x y eq -> do
    aTy <- infer ctx a
    case normalize aTy of
      Universe i -> do
        check ctx x a
        check ctx y a
        check ctx eq (Eq a x y)
        let cTy =
              Pi "z" a
                (Pi "e" (Eq a x (Var "z"))
                  (Universe i))
        check ctx c cTy
        check ctx p (App (App c x) (Refl x))
        Right (App (App c y) eq)
      _ -> Left (NotAType a)
  Match {} -> Left (NotSupported "match")
  Ind {} -> Left (NotSupported "inductive types")
  Con {} -> Left (NotSupported "constructors")

check :: Context -> Term -> Term -> Either TypeError ()
check ctx term expected =
  case (term, normalize expected) of
    (Lam x ty body, Pi y a b) -> do
      checkType ctx ty
      if typeEq ty a
        then check (extendCtx x a ctx) body (subst y (Var x) b)
        else Left (TypeMismatch a ty)
    (Pair t1 t2, Sigma x a b) -> do
      check ctx t1 a
      check ctx t2 (subst x t1 b)
    _ -> do
      ty <- infer ctx term
      if typeEq expected ty
        then Right ()
        else Left (TypeMismatch expected ty)

checkType :: Context -> Term -> Either TypeError ()
checkType ctx t = do
  ty <- infer ctx t
  case normalize ty of
    Universe _ -> Right ()
    _ -> Left (NotAType t)
