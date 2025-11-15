module Pretty (pretty, prettyType) where

import Syntax

prettyType :: Type -> String
prettyType = prettyTypePrec 0

prettyTypePrec :: Int -> Type -> String
prettyTypePrec _ (TyVar a) = a
prettyTypePrec p (TyArr t1 t2) =
  parensIf (p > 0) $ prettyTypePrec 1 t1 ++ " -> " ++ prettyTypePrec 0 t2
prettyTypePrec p (TyForall a t) =
  parensIf (p > 0) $ "∀" ++ a ++ ". " ++ prettyTypePrec 0 t
prettyTypePrec _ TyBool = "Bool"
prettyTypePrec _ TyNat = "Nat"

pretty :: Term -> String
pretty = prettyPrec 0

prettyPrec :: Int -> Term -> String
prettyPrec _ (Var x) = x
prettyPrec p (Lam x ty t) =
  parensIf (p > 0) $ "λ" ++ x ++ ":" ++ prettyType ty ++ ". " ++ prettyPrec 0 t
prettyPrec p (App t1 t2) =
  parensIf (p > 1) $ prettyPrec 1 t1 ++ " " ++ prettyPrec 2 t2
prettyPrec p (TyAbs a t) =
  parensIf (p > 0) $ "Λ" ++ a ++ ". " ++ prettyPrec 0 t
prettyPrec p (TyApp t ty) =
  parensIf (p > 1) $ prettyPrec 1 t ++ " [" ++ prettyType ty ++ "]"
prettyPrec _ TmTrue = "true"
prettyPrec _ TmFalse = "false"
prettyPrec p (TmIf t1 t2 t3) =
  parensIf (p > 0) $
    "if " ++ pretty t1 ++ " then " ++ pretty t2 ++ " else " ++ pretty t3
prettyPrec _ TmZero = "0"
prettyPrec p (TmSucc t) = parensIf (p > 1) $ "succ " ++ prettyPrec 2 t
prettyPrec p (TmPred t) = parensIf (p > 1) $ "pred " ++ prettyPrec 2 t
prettyPrec p (TmIsZero t) = parensIf (p > 1) $ "iszero " ++ prettyPrec 2 t

parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s
