{-# LANGUAGE LambdaCase #-}

module Pretty
  ( -- * Pretty printing
    prettyTerm
  , prettyType
  , prettyPred
  , prettyArith
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

  TmArith op t1 t2 ->
    prettyTermAtom t1 ++ " " ++ prettyArithOp op ++ " " ++ prettyTermAtom t2

  TmUnit -> "()"

  TmLet x t1 t2 ->
    "let " ++ x ++ " = " ++ prettyTerm t1 ++ " in " ++ prettyTerm t2

  TmAscribe t ty ->
    prettyTermAtom t ++ " : " ++ prettyType ty

-- | Pretty print for application position (no parens for applications)
prettyTermApp :: Term -> String
prettyTermApp t@(App _ _) = prettyTerm t
prettyTermApp t@(Var _) = prettyTerm t
prettyTermApp t = "(" ++ prettyTerm t ++ ")"

-- | Pretty print for atomic position (add parens if needed)
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

prettyArithOp :: ArithOp -> String
prettyArithOp Add = "+"
prettyArithOp Sub = "-"

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
  TyBase TyBool -> "Bool"
  TyBase TyNat -> "Nat"
  TyBase TyUnit -> "Unit"

  TyRefine x ty p ->
    "{" ++ x ++ " : " ++ prettyType ty ++ " | " ++ prettyPred p ++ "}"

  TyFun x ty1 ty2
    | x == "_" -> prettyTypeAtom ty1 ++ " -> " ++ prettyType ty2
    | otherwise -> "(" ++ x ++ " : " ++ prettyType ty1 ++ ") -> " ++ prettyType ty2

-- | Pretty print for atomic position
prettyTypeAtom :: Type -> String
prettyTypeAtom t@(TyBase _) = prettyType t
prettyTypeAtom t@(TyRefine {}) = prettyType t
prettyTypeAtom t = "(" ++ prettyType t ++ ")"

-- =============================================================================
-- Pretty Printing Predicates
-- =============================================================================

prettyPred :: Pred -> String
prettyPred = \case
  PTrue -> "true"
  PFalse -> "false"
  PVar x -> x
  PNot p -> "!" ++ prettyPredAtom p
  PAnd p1 p2 -> prettyPredAtom p1 ++ " && " ++ prettyPredAtom p2
  POr p1 p2 -> prettyPredAtom p1 ++ " || " ++ prettyPredAtom p2
  PImpl p1 p2 -> prettyPredAtom p1 ++ " => " ++ prettyPred p2
  PComp op a1 a2 -> prettyArith a1 ++ " " ++ prettyCompOp op ++ " " ++ prettyArith a2

prettyPredAtom :: Pred -> String
prettyPredAtom p@PTrue = prettyPred p
prettyPredAtom p@PFalse = prettyPred p
prettyPredAtom p@(PVar _) = prettyPred p
prettyPredAtom p@(PComp {}) = prettyPred p
prettyPredAtom p = "(" ++ prettyPred p ++ ")"

prettyCompOp :: CompOp -> String
prettyCompOp = \case
  OpEq -> "=="
  OpNeq -> "!="
  OpLt -> "<"
  OpLe -> "<="
  OpGt -> ">"
  OpGe -> ">="

-- =============================================================================
-- Pretty Printing Arithmetic
-- =============================================================================

prettyArith :: PArith -> String
prettyArith = \case
  PAVar x -> x
  PALit n -> show n
  PAAdd a1 a2 -> prettyArithAtom a1 ++ " + " ++ prettyArithAtom a2
  PASub a1 a2 -> prettyArithAtom a1 ++ " - " ++ prettyArithAtom a2
  PAMul n a -> show n ++ " * " ++ prettyArithAtom a

prettyArithAtom :: PArith -> String
prettyArithAtom a@(PAVar _) = prettyArith a
prettyArithAtom a@(PALit _) = prettyArith a
prettyArithAtom a = "(" ++ prettyArith a ++ ")"
