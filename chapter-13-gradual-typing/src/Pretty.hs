{-# LANGUAGE LambdaCase #-}

module Pretty
  ( -- * Pretty printing
    prettyTerm
  , prettyType
  ) where

import Syntax

-- =============================================================================
-- Pretty Printing Terms
-- =============================================================================

prettyTerm :: Term -> String
prettyTerm = \case
  Var x -> x

  Lam x ty t ->
    "λ" ++ x ++ " : " ++ prettyType ty ++ ". " ++ prettyTerm t

  App t1 t2 ->
    prettyTermApp t1 ++ " " ++ prettyTermAtom t2

  TmTrue -> "true"
  TmFalse -> "false"

  TmIf t1 t2 t3 ->
    "if " ++ prettyTerm t1 ++
    " then " ++ prettyTerm t2 ++
    " else " ++ prettyTerm t3

  TmZero -> "0"

  TmSucc t -> case termToNat (TmSucc t) of
    Just n -> show n
    Nothing -> "succ " ++ prettyTermAtom t

  TmPred t -> "pred " ++ prettyTermAtom t

  TmIsZero t -> "iszero " ++ prettyTermAtom t

  TmUnit -> "()"

  TmLet x t1 t2 ->
    "let " ++ x ++ " = " ++ prettyTerm t1 ++ " in " ++ prettyTerm t2

  TmCast t ty1 ty2 l ->
    "<" ++ prettyType ty1 ++ " => " ++ prettyType ty2 ++ ">^" ++ l ++
    " " ++ prettyTermAtom t

  TmAscribe t ty ->
    prettyTermAtom t ++ " : " ++ prettyType ty

  TmBlame ty l ->
    "blame^" ++ l ++ " : " ++ prettyType ty

-- | Pretty print for application position
prettyTermApp :: Term -> String
prettyTermApp t@(App _ _) = prettyTerm t
prettyTermApp t@(Var _) = prettyTerm t
prettyTermApp t = "(" ++ prettyTerm t ++ ")"

-- | Pretty print for atomic position
prettyTermAtom :: Term -> String
prettyTermAtom t@(Var _) = prettyTerm t
prettyTermAtom TmTrue = "true"
prettyTermAtom TmFalse = "false"
prettyTermAtom TmZero = "0"
prettyTermAtom TmUnit = "()"
prettyTermAtom t@(TmSucc _) = case termToNat t of
  Just n -> show n
  Nothing -> "(" ++ prettyTerm t ++ ")"
prettyTermAtom t = "(" ++ prettyTerm t ++ ")"

-- | Try to convert a term to a natural number
termToNat :: Term -> Maybe Int
termToNat = \case
  TmZero -> Just 0
  TmSucc t -> (+ 1) <$> termToNat t
  _ -> Nothing

-- =============================================================================
-- Pretty Printing Types
-- =============================================================================

prettyType :: Type -> String
prettyType = \case
  TyBool -> "Bool"
  TyNat -> "Nat"
  TyUnit -> "Unit"
  TyDyn -> "?"
  TyFun t1 t2 -> prettyTypeAtom t1 ++ " -> " ++ prettyType t2

-- | Pretty print for atomic position
prettyTypeAtom :: Type -> String
prettyTypeAtom t@TyBool = prettyType t
prettyTypeAtom t@TyNat = prettyType t
prettyTypeAtom t@TyUnit = prettyType t
prettyTypeAtom t@TyDyn = prettyType t
prettyTypeAtom t = "(" ++ prettyType t ++ ")"
