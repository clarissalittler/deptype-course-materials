{-# LANGUAGE LambdaCase #-}

module Pretty
  ( -- * Pretty printing
    prettyTerm
  , prettyType
  , prettyEffectRow
  , prettyHandler
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

  TmPerform eff op t ->
    "perform " ++ eff ++ "." ++ op ++ " " ++ prettyTermAtom t

  TmHandle t h ->
    "handle " ++ prettyTermAtom t ++ " with " ++ prettyHandler h

  TmEffAbs v t ->
    "Λ" ++ v ++ ". " ++ prettyTerm t

  TmEffApp t eff ->
    prettyTermAtom t ++ " [" ++ prettyEffectRow eff ++ "]"

  TmReturn t ->
    "return " ++ prettyTermAtom t

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
  TyUnit -> "Unit"
  TyBool -> "Bool"
  TyNat -> "Nat"

  TyFun t1 t2 eff ->
    prettyTypeAtom t1 ++ " -> " ++ prettyType t2 ++
    (if isEmptyRow eff then "" else " ! " ++ prettyEffectRow eff)

  TyForallEff v t ->
    "∀" ++ v ++ ". " ++ prettyType t

-- | Pretty print for atomic position
prettyTypeAtom :: Type -> String
prettyTypeAtom t@TyUnit = prettyType t
prettyTypeAtom t@TyBool = prettyType t
prettyTypeAtom t@TyNat = prettyType t
prettyTypeAtom t = "(" ++ prettyType t ++ ")"

-- =============================================================================
-- Pretty Printing Effect Rows
-- =============================================================================

prettyEffectRow :: EffectRow -> String
prettyEffectRow eff = "{" ++ prettyRowInner eff ++ "}"

prettyRowInner :: EffectRow -> String
prettyRowInner = \case
  EffEmpty -> ""
  EffLabel l EffEmpty -> l
  EffLabel l (EffVar v) -> l ++ " | " ++ v
  EffLabel l r -> l ++ ", " ++ prettyRowInner r
  EffVar v -> v

-- | Check if effect row is empty
isEmptyRow :: EffectRow -> Bool
isEmptyRow EffEmpty = True
isEmptyRow _ = False

-- =============================================================================
-- Pretty Printing Handlers
-- =============================================================================

prettyHandler :: Handler -> String
prettyHandler h =
  "{ " ++ handlerEffect h ++ ": " ++
  prettyReturnClause (handlerReturn h) ++
  concatMap prettyOpClause (handlerOps h) ++
  " }"

prettyReturnClause :: (Var, Term) -> String
prettyReturnClause (x, body) =
  "return " ++ x ++ " -> " ++ prettyTerm body ++ "; "

prettyOpClause :: (String, Var, Var, Term) -> String
prettyOpClause (op, param, cont, body) =
  op ++ " " ++ param ++ " " ++ cont ++ " -> " ++ prettyTerm body ++ "; "
