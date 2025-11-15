module Pretty (pretty, prettyType, prettyScheme) where

import Syntax

prettyType :: Type -> String
prettyType = prettyTypePrec 0

prettyTypePrec :: Int -> Type -> String
prettyTypePrec _ (TyVar a) = a
prettyTypePrec p (TyArr t1 t2) =
  parensIf (p > 0) $ prettyTypePrec 1 t1 ++ " -> " ++ prettyTypePrec 0 t2
prettyTypePrec _ TyBool = "Bool"
prettyTypePrec _ TyNat = "Nat"
prettyTypePrec p (TyProd t1 t2) =
  parensIf (p > 1) $ prettyTypePrec 2 t1 ++ " * " ++ prettyTypePrec 2 t2
prettyTypePrec p (TyList t) =
  parensIf (p > 2) $ "List " ++ prettyTypePrec 3 t

prettyScheme :: TypeScheme -> String
prettyScheme (TypeScheme [] ty) = prettyType ty
prettyScheme (TypeScheme vars ty) =
  "∀" ++ unwords vars ++ ". " ++ prettyType ty

pretty :: Term -> String
pretty = prettyPrec 0

prettyPrec :: Int -> Term -> String
prettyPrec _ (Var x) = x
prettyPrec p (Lam x t) =
  parensIf (p > 0) $ "λ" ++ x ++ ". " ++ prettyPrec 0 t
prettyPrec p (App t1 t2) =
  parensIf (p > 1) $ prettyPrec 1 t1 ++ " " ++ prettyPrec 2 t2
prettyPrec p (Let x t1 t2) =
  parensIf (p > 0) $ "let " ++ x ++ " = " ++ pretty t1 ++ " in " ++ pretty t2
prettyPrec _ TmTrue = "true"
prettyPrec _ TmFalse = "false"
prettyPrec p (TmIf t1 t2 t3) =
  parensIf (p > 0) $
    "if " ++ pretty t1 ++ " then " ++ pretty t2 ++ " else " ++ pretty t3
prettyPrec _ TmZero = "0"
prettyPrec p (TmSucc t) = parensIf (p > 1) $ "succ " ++ prettyPrec 2 t
prettyPrec p (TmPred t) = parensIf (p > 1) $ "pred " ++ prettyPrec 2 t
prettyPrec p (TmIsZero t) = parensIf (p > 1) $ "iszero " ++ prettyPrec 2 t
prettyPrec _ (TmPair t1 t2) = "(" ++ pretty t1 ++ ", " ++ pretty t2 ++ ")"
prettyPrec p (TmFst t) = parensIf (p > 1) $ "fst " ++ prettyPrec 2 t
prettyPrec p (TmSnd t) = parensIf (p > 1) $ "snd " ++ prettyPrec 2 t
prettyPrec _ TmNil = "[]"
prettyPrec p (TmCons t1 t2) =
  parensIf (p > 1) $ prettyPrec 2 t1 ++ " :: " ++ prettyPrec 1 t2
prettyPrec p (TmIsNil t) = parensIf (p > 1) $ "isnil " ++ prettyPrec 2 t
prettyPrec p (TmHead t) = parensIf (p > 1) $ "head " ++ prettyPrec 2 t
prettyPrec p (TmTail t) = parensIf (p > 1) $ "tail " ++ prettyPrec 2 t

parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s
