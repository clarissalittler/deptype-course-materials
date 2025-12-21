{-# LANGUAGE LambdaCase #-}

module Pretty
  ( prettyTerm
  , prettyType
  , prettyRow
  ) where

import Syntax
import qualified Data.Map as Map

prettyTerm :: Term -> String
prettyTerm = \case
  Var x -> x
  Lam x ty t -> "λ" ++ x ++ " : " ++ prettyType ty ++ ". " ++ prettyTerm t
  App t1 t2 -> prettyTermApp t1 ++ " " ++ prettyTermAtom t2
  TmTrue -> "true"
  TmFalse -> "false"
  TmIf t1 t2 t3 -> "if " ++ prettyTerm t1 ++ " then " ++ prettyTerm t2 ++ " else " ++ prettyTerm t3
  TmZero -> "0"
  TmSucc t -> case termToNat (TmSucc t) of
    Just n -> show n
    Nothing -> "succ " ++ prettyTermAtom t
  TmPred t -> "pred " ++ prettyTermAtom t
  TmIsZero t -> "iszero " ++ prettyTermAtom t
  TmUnit -> "()"
  TmRecord fields -> "{" ++ intercalate ", " [l ++ " = " ++ prettyTerm t | (l, t) <- Map.toList fields] ++ "}"
  TmProj t l -> prettyTermAtom t ++ "." ++ l
  TmExtend t1 l t2 -> "{" ++ l ++ " = " ++ prettyTerm t2 ++ " | " ++ prettyTermAtom t1 ++ "}"
  TmRestrict t l -> prettyTermAtom t ++ " \\ " ++ l
  TmVariant l t ty -> "<" ++ l ++ " = " ++ prettyTerm t ++ "> : " ++ prettyType ty
  TmCase t cases -> "case " ++ prettyTerm t ++ " of " ++ intercalate " | " (map prettyCase cases)
  TmLet x t1 t2 -> "let " ++ x ++ " = " ++ prettyTerm t1 ++ " in " ++ prettyTerm t2
  TmRowAbs v t -> "Λ" ++ v ++ ". " ++ prettyTerm t
  TmRowApp t r -> prettyTermAtom t ++ " [" ++ prettyRow r ++ "]"

prettyCase :: (Label, Var, Term) -> String
prettyCase (l, x, body) = "<" ++ l ++ " = " ++ x ++ "> -> " ++ prettyTerm body

prettyTermApp :: Term -> String
prettyTermApp t@(App _ _) = prettyTerm t
prettyTermApp t@(Var _) = prettyTerm t
prettyTermApp t = "(" ++ prettyTerm t ++ ")"

prettyTermAtom :: Term -> String
prettyTermAtom t@(Var _) = prettyTerm t
prettyTermAtom TmTrue = "true"
prettyTermAtom TmFalse = "false"
prettyTermAtom TmZero = "0"
prettyTermAtom TmUnit = "()"
prettyTermAtom t@(TmSucc _) = case termToNat t of
  Just n -> show n
  Nothing -> "(" ++ prettyTerm t ++ ")"
prettyTermAtom t@(TmRecord _) = prettyTerm t
prettyTermAtom t = "(" ++ prettyTerm t ++ ")"

termToNat :: Term -> Maybe Int
termToNat TmZero = Just 0
termToNat (TmSucc t) = (+ 1) <$> termToNat t
termToNat _ = Nothing

prettyType :: Type -> String
prettyType = \case
  TyBool -> "Bool"
  TyNat -> "Nat"
  TyUnit -> "Unit"
  TyFun t1 t2 -> prettyTypeAtom t1 ++ " -> " ++ prettyType t2
  TyRecord r -> "{" ++ prettyRow r ++ "}"
  TyVariant r -> "<" ++ prettyRow r ++ ">"
  TyForallRow v t -> "∀" ++ v ++ ". " ++ prettyType t

prettyTypeAtom :: Type -> String
prettyTypeAtom t@TyBool = prettyType t
prettyTypeAtom t@TyNat = prettyType t
prettyTypeAtom t@TyUnit = prettyType t
prettyTypeAtom t@(TyRecord _) = prettyType t
prettyTypeAtom t@(TyVariant _) = prettyType t
prettyTypeAtom t = "(" ++ prettyType t ++ ")"

prettyRow :: Row -> String
prettyRow RowEmpty = ""
prettyRow (RowExtend l ty RowEmpty) = l ++ ": " ++ prettyType ty
prettyRow (RowExtend l ty (RowVar v)) = l ++ ": " ++ prettyType ty ++ " | " ++ v
prettyRow (RowExtend l ty r) = l ++ ": " ++ prettyType ty ++ ", " ++ prettyRow r
prettyRow (RowVar v) = v

intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs
