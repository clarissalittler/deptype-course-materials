{-# LANGUAGE LambdaCase #-}

module Pretty
  ( prettyTerm
  , prettyType
  , prettyMult
  ) where

import Syntax

-- =============================================================================
-- Pretty Printing Types
-- =============================================================================

prettyType :: Type -> String
prettyType = \case
  TyVar v -> v
  TyBool -> "Bool"
  TyNat -> "Nat"
  TyUnit -> "()"
  TyFun One t1 t2 -> prettyTypeArg t1 ++ " -o " ++ prettyType t2
  TyFun Many t1 t2 -> prettyTypeArg t1 ++ " -> " ++ prettyType t2
  TyPair t1 t2 -> prettyTypeArg t1 ++ " * " ++ prettyTypeArg t2
  TyBang t -> "!" ++ prettyTypeAtom t

prettyTypeArg :: Type -> String
prettyTypeArg t@(TyFun {}) = "(" ++ prettyType t ++ ")"
prettyTypeArg t = prettyType t

prettyTypeAtom :: Type -> String
prettyTypeAtom t@(TyFun {}) = "(" ++ prettyType t ++ ")"
prettyTypeAtom t@(TyPair {}) = "(" ++ prettyType t ++ ")"
prettyTypeAtom t = prettyType t

-- =============================================================================
-- Pretty Printing Multiplicities
-- =============================================================================

prettyMult :: Mult -> String
prettyMult One = "1"
prettyMult Many = "ω"

-- =============================================================================
-- Pretty Printing Terms
-- =============================================================================

prettyTerm :: Term -> String
prettyTerm = go
  where
    go = \case
      Var x -> x
      Lam x m ty t ->
        "λ" ++ x ++ " :" ++ prettyMult m ++ " " ++ prettyType ty ++ ". " ++ go t
      App t1 t2 -> goApp t1 ++ " " ++ goArg t2
      TmTrue -> "true"
      TmFalse -> "false"
      TmIf t1 t2 t3 ->
        "if " ++ go t1 ++ " then " ++ go t2 ++ " else " ++ go t3
      TmZero -> "0"
      TmSucc t -> case toNat (TmSucc t) of
        Just n -> show n
        Nothing -> "succ " ++ goArg t
      TmPred t -> "pred " ++ goArg t
      TmIsZero t -> "iszero " ++ goArg t
      TmUnit -> "()"
      TmPair t1 t2 -> "(" ++ go t1 ++ ", " ++ go t2 ++ ")"
      TmLetPair x y t1 t2 ->
        "let (" ++ x ++ ", " ++ y ++ ") = " ++ go t1 ++ " in " ++ go t2
      TmBang t -> "!" ++ goArg t
      TmLetBang x t1 t2 ->
        "let !" ++ x ++ " = " ++ go t1 ++ " in " ++ go t2
      TmLet x m t1 t2 ->
        "let " ++ x ++ " :" ++ prettyMult m ++ " = " ++ go t1 ++ " in " ++ go t2

    goApp = \case
      App t1 t2 -> goApp t1 ++ " " ++ goArg t2
      t -> go t

    goArg = \case
      t@(Var _) -> go t
      t@TmTrue -> go t
      t@TmFalse -> go t
      t@TmZero -> go t
      t@(TmSucc _) -> case toNat t of
        Just n -> show n
        Nothing -> "(" ++ go t ++ ")"
      t@TmUnit -> go t
      t@(TmPair {}) -> go t
      t@(TmBang _) -> go t
      t -> "(" ++ go t ++ ")"

toNat :: Term -> Maybe Int
toNat TmZero = Just 0
toNat (TmSucc t) = (+ 1) <$> toNat t
toNat _ = Nothing
