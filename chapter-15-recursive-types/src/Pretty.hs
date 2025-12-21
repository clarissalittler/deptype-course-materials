module Pretty (prettyTerm, prettyType) where

import Syntax

prettyType :: Type -> String
prettyType = go 0
  where
    go :: Int -> Type -> String
    go _ (TyVar v) = v
    go _ TyBool = "Bool"
    go _ TyNat = "Nat"
    go _ TyUnit = "Unit"
    go p (TyFun t1 t2) = paren (p > 0) $ go 1 t1 ++ " -> " ++ go 0 t2
    go p (TyProd t1 t2) = paren (p > 1) $ go 2 t1 ++ " * " ++ go 1 t2
    go p (TySum t1 t2) = paren (p > 1) $ go 2 t1 ++ " + " ++ go 1 t2
    go p (TyMu v t) = paren (p > 0) $ "μ" ++ v ++ ". " ++ go 0 t

    paren :: Bool -> String -> String
    paren True s = "(" ++ s ++ ")"
    paren False s = s

prettyTerm :: Term -> String
prettyTerm = go 0
  where
    go :: Int -> Term -> String
    go _ (Var x) = x
    go p (Lam x ty t) = paren (p > 0) $ "λ" ++ x ++ ":" ++ prettyType ty ++ ". " ++ go 0 t
    go p (App t1 t2) = paren (p > 1) $ go 1 t1 ++ " " ++ go 2 t2
    go _ TmTrue = "true"
    go _ TmFalse = "false"
    go p (TmIf t1 t2 t3) = paren (p > 0) $
      "if " ++ go 0 t1 ++ " then " ++ go 0 t2 ++ " else " ++ go 0 t3
    go _ TmZero = "0"
    go p (TmSucc t) = paren (p > 1) $ "succ " ++ go 2 t
    go p (TmPred t) = paren (p > 1) $ "pred " ++ go 2 t
    go p (TmIsZero t) = paren (p > 1) $ "iszero " ++ go 2 t
    go _ TmUnit = "unit"
    go _ (TmPair t1 t2) = "<" ++ go 0 t1 ++ ", " ++ go 0 t2 ++ ">"
    go p (TmFst t) = paren (p > 1) $ "fst " ++ go 2 t
    go p (TmSnd t) = paren (p > 1) $ "snd " ++ go 2 t
    go p (TmInl t ty) = paren (p > 0) $ "inl " ++ go 2 t ++ " as " ++ prettyType ty
    go p (TmInr t ty) = paren (p > 0) $ "inr " ++ go 2 t ++ " as " ++ prettyType ty
    go p (TmCase t x1 t1 x2 t2) = paren (p > 0) $
      "case " ++ go 0 t ++ " of inl " ++ x1 ++ " => " ++ go 0 t1 ++
      " | inr " ++ x2 ++ " => " ++ go 0 t2
    go p (TmLet x t1 t2) = paren (p > 0) $
      "let " ++ x ++ " = " ++ go 0 t1 ++ " in " ++ go 0 t2
    go p (TmFold ty t) = paren (p > 1) $ "fold [" ++ prettyType ty ++ "] " ++ go 2 t
    go p (TmUnfold ty t) = paren (p > 1) $ "unfold [" ++ prettyType ty ++ "] " ++ go 2 t

    paren :: Bool -> String -> String
    paren True s = "(" ++ s ++ ")"
    paren False s = s
