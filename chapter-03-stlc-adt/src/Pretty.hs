{-# LANGUAGE LambdaCase #-}

module Pretty
  ( pretty
  , prettyType
  , prettyPattern
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.List (intercalate)

-- Pretty-print a type
prettyType :: Type -> String
prettyType = prettyTypePrec 0

prettyTypePrec :: Int -> Type -> String
prettyTypePrec _ (TyVar x) = x
prettyTypePrec p (TyArr t1 t2) =
  parensIf (p > 0) $ prettyTypePrec 1 t1 ++ " -> " ++ prettyTypePrec 0 t2
prettyTypePrec _ TyBool = "Bool"
prettyTypePrec _ TyNat = "Nat"
prettyTypePrec _ TyUnit = "Unit"
prettyTypePrec p (TyProd t1 t2) =
  parensIf (p > 1) $ prettyTypePrec 2 t1 ++ " * " ++ prettyTypePrec 2 t2
prettyTypePrec p (TySum t1 t2) =
  parensIf (p > 1) $ prettyTypePrec 2 t1 ++ " + " ++ prettyTypePrec 2 t2
prettyTypePrec _ (TyRecord fields) =
  "{" ++ intercalate ", " [l ++ ":" ++ prettyType ty | (l, ty) <- Map.toList fields] ++ "}"
prettyTypePrec _ (TyVariant fields) =
  "<" ++ intercalate ", " [l ++ ":" ++ prettyType ty | (l, ty) <- Map.toList fields] ++ ">"
prettyTypePrec p (TyList ty) =
  parensIf (p > 2) $ "List " ++ prettyTypePrec 3 ty

-- Pretty-print a pattern
prettyPattern :: Pattern -> String
prettyPattern = \case
  PatVar x -> x
  PatWild -> "_"
  PatUnit -> "()"
  PatTrue -> "true"
  PatFalse -> "false"
  PatZero -> "0"
  PatSucc p -> "succ " ++ prettyPattern p
  PatPair p1 p2 -> "(" ++ prettyPattern p1 ++ ", " ++ prettyPattern p2 ++ ")"
  PatInl p -> "inl " ++ prettyPattern p
  PatInr p -> "inr " ++ prettyPattern p
  PatVariant l p -> "<" ++ l ++ "=" ++ prettyPattern p ++ ">"
  PatNil -> "[]"
  PatCons p ps -> prettyPattern p ++ "::" ++ prettyPattern ps

-- Pretty-print a term
pretty :: Term -> String
pretty = prettyPrec 0

prettyPrec :: Int -> Term -> String
prettyPrec _ (Var x) = x

prettyPrec p (Lam x ty t) =
  parensIf (p > 0) $ "λ" ++ x ++ ":" ++ prettyType ty ++ ". " ++ prettyPrec 0 t

prettyPrec p (App t1 t2) =
  parensIf (p > 1) $ prettyPrec 1 t1 ++ " " ++ prettyPrec 2 t2

prettyPrec _ TmTrue = "true"
prettyPrec _ TmFalse = "false"

prettyPrec p (TmIf t1 t2 t3) =
  parensIf (p > 0) $
    "if " ++ pretty t1 ++ " then " ++ pretty t2 ++ " else " ++ pretty t3

prettyPrec _ TmZero = "0"
prettyPrec p (TmSucc t) = parensIf (p > 1) $ "succ " ++ prettyPrec 2 t
prettyPrec p (TmPred t) = parensIf (p > 1) $ "pred " ++ prettyPrec 2 t
prettyPrec p (TmIsZero t) = parensIf (p > 1) $ "iszero " ++ prettyPrec 2 t

prettyPrec _ TmUnit = "()"

prettyPrec _ (TmPair t1 t2) =
  "(" ++ pretty t1 ++ ", " ++ pretty t2 ++ ")"

prettyPrec p (TmFst t) = parensIf (p > 1) $ "fst " ++ prettyPrec 2 t
prettyPrec p (TmSnd t) = parensIf (p > 1) $ "snd " ++ prettyPrec 2 t

prettyPrec p (TmInl ty t) =
  parensIf (p > 1) $ "inl[" ++ prettyType ty ++ "] " ++ prettyPrec 2 t

prettyPrec p (TmInr ty t) =
  parensIf (p > 1) $ "inr[" ++ prettyType ty ++ "] " ++ prettyPrec 2 t

prettyPrec p (TmCase t x1 t1 x2 t2) =
  parensIf (p > 0) $
    "case " ++ pretty t ++ " of inl " ++ x1 ++ " => " ++ pretty t1 ++
    " | inr " ++ x2 ++ " => " ++ pretty t2

prettyPrec _ (TmRecord fields) =
  "{" ++ intercalate ", " [l ++ "=" ++ pretty t | (l, t) <- Map.toList fields] ++ "}"

prettyPrec p (TmProj t label) =
  parensIf (p > 2) $ prettyPrec 2 t ++ "." ++ label

prettyPrec p (TmTag label t ty) =
  parensIf (p > 1) $ "<" ++ label ++ "=" ++ pretty t ++ "> as " ++ prettyType ty

prettyPrec p (TmCaseVariant t cases) =
  parensIf (p > 0) $
    "case " ++ pretty t ++ " of " ++
    intercalate " | " ["<" ++ l ++ "=" ++ x ++ "> => " ++ pretty ti | (l, x, ti) <- cases]

prettyPrec p (TmNil ty) =
  "[]:" ++ prettyType ty

prettyPrec p (TmCons t ts) =
  parensIf (p > 1) $ prettyPrec 2 t ++ "::" ++ prettyPrec 1 ts

prettyPrec p (TmIsNil t) = parensIf (p > 1) $ "isnil " ++ prettyPrec 2 t
prettyPrec p (TmHead t) = parensIf (p > 1) $ "head " ++ prettyPrec 2 t
prettyPrec p (TmTail t) = parensIf (p > 1) $ "tail " ++ prettyPrec 2 t

prettyPrec p (TmMatch t cases) =
  parensIf (p > 0) $
    "match " ++ pretty t ++ " with " ++
    intercalate " | " [prettyPattern pat ++ " => " ++ pretty ti | (pat, ti) <- cases]

-- Add parentheses if needed
parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s
