{-# LANGUAGE LambdaCase #-}

module Eval (eval, evalStep, isValue) where

import Syntax

isValue :: Term -> Bool
isValue = \case
  Lam {} -> True
  TmTrue -> True
  TmFalse -> True
  TmZero -> True
  TmSucc t -> isNumericValue t
  TmUnit -> True
  TmPair t1 t2 -> isValue t1 && isValue t2
  TmInl t _ -> isValue t
  TmInr t _ -> isValue t
  TmRefl {} -> True  -- refl is a value (a path constructor)
  _ -> False

isNumericValue :: Term -> Bool
isNumericValue TmZero = True
isNumericValue (TmSucc t) = isNumericValue t
isNumericValue _ = False

eval :: Term -> Term
eval t = maybe t eval (evalStep t)

evalStep :: Term -> Maybe Term
evalStep = \case
  App t1 t2
    | not (isValue t1) -> App <$> evalStep t1 <*> pure t2
    | not (isValue t2) -> App t1 <$> evalStep t2
    | Lam x _ body <- t1 -> Just $ substVar x t2 body
    | otherwise -> Nothing

  TmIf t1 t2 t3
    | not (isValue t1) -> (\t' -> TmIf t' t2 t3) <$> evalStep t1
    | TmTrue <- t1 -> Just t2
    | TmFalse <- t1 -> Just t3
    | otherwise -> Nothing

  TmSucc t
    | not (isValue t) -> TmSucc <$> evalStep t
    | otherwise -> Nothing

  TmPred t
    | not (isValue t) -> TmPred <$> evalStep t
    | TmZero <- t -> Just TmZero
    | TmSucc n <- t, isNumericValue n -> Just n
    | otherwise -> Nothing

  TmIsZero t
    | not (isValue t) -> TmIsZero <$> evalStep t
    | TmZero <- t -> Just TmTrue
    | TmSucc n <- t, isNumericValue n -> Just TmFalse
    | otherwise -> Nothing

  TmAbsurd ty t
    | not (isValue t) -> TmAbsurd ty <$> evalStep t
    | otherwise -> Nothing  -- Stuck: no value of Void type

  TmPair t1 t2
    | not (isValue t1) -> TmPair <$> evalStep t1 <*> pure t2
    | not (isValue t2) -> TmPair t1 <$> evalStep t2
    | otherwise -> Nothing

  TmFst t
    | not (isValue t) -> TmFst <$> evalStep t
    | TmPair v1 _ <- t, isValue v1 -> Just v1
    | otherwise -> Nothing

  TmSnd t
    | not (isValue t) -> TmSnd <$> evalStep t
    | TmPair _ v2 <- t, isValue v2 -> Just v2
    | otherwise -> Nothing

  TmInl t ty
    | not (isValue t) -> (\t' -> TmInl t' ty) <$> evalStep t
    | otherwise -> Nothing

  TmInr t ty
    | not (isValue t) -> (\t' -> TmInr t' ty) <$> evalStep t
    | otherwise -> Nothing

  TmCase t x1 t1 x2 t2
    | not (isValue t) -> (\t' -> TmCase t' x1 t1 x2 t2) <$> evalStep t
    | TmInl v _ <- t -> Just $ substVar x1 v t1
    | TmInr v _ <- t -> Just $ substVar x2 v t2
    | otherwise -> Nothing

  TmLet x t1 t2
    | not (isValue t1) -> (\t' -> TmLet x t' t2) <$> evalStep t1
    | otherwise -> Just $ substVar x t1 t2

  -- refl evaluates its argument
  TmRefl ty t
    | not (isValue t) -> TmRefl ty <$> evalStep t
    | otherwise -> Nothing  -- refl v is a value

  -- J eliminator: J C base a a refl ≡ base a
  -- This is the computation rule for path induction
  TmJ ty base a b p
    | not (isValue a) -> (\a' -> TmJ ty base a' b p) <$> evalStep a
    | not (isValue b) -> (\b' -> TmJ ty base a b' p) <$> evalStep b
    | not (isValue p) -> (\p' -> TmJ ty base a b p') <$> evalStep p
    | TmRefl _ a' <- p, a == b, a == a' ->
        -- J C base a a refl ≡ base a
        Just $ App base a
    | otherwise -> Nothing

  -- sym refl ≡ refl
  TmSym t
    | not (isValue t) -> TmSym <$> evalStep t
    | TmRefl ty a <- t -> Just $ TmRefl ty a
    | otherwise -> Nothing

  -- trans refl refl ≡ refl
  TmTrans t1 t2
    | not (isValue t1) -> (\t' -> TmTrans t' t2) <$> evalStep t1
    | not (isValue t2) -> TmTrans t1 <$> evalStep t2
    | TmRefl ty a <- t1, TmRefl _ _ <- t2 -> Just $ TmRefl ty a
    | otherwise -> Nothing

  -- ap f refl ≡ refl
  TmAp f p
    | not (isValue f) -> (\f' -> TmAp f' p) <$> evalStep f
    | not (isValue p) -> TmAp f <$> evalStep p
    | TmRefl tyA a <- p -> Just $ TmRefl tyA (App f a)  -- ap f refl = refl
    | otherwise -> Nothing

  -- transport refl t ≡ t
  TmTransport ty p t
    | not (isValue p) -> (\p' -> TmTransport ty p' t) <$> evalStep p
    | not (isValue t) -> TmTransport ty p <$> evalStep t
    | TmRefl _ _ <- p -> Just t  -- transport refl t = t
    | otherwise -> Nothing

  _ -> Nothing
