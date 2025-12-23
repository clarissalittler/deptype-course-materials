-- | Pretty printer for bidirectional terms

module Pretty
  ( prettyTerm
  , prettyType
  , prettyVal
  ) where

import Syntax

-- | Pretty print a type
prettyType :: Type -> String
prettyType = go 0
  where
    go :: Int -> Type -> String
    go _ (TyVar a) = a
    go _ TyBool = "Bool"
    go _ TyNat = "Nat"
    go _ TyUnit = "Unit"
    go p (TyArr a b) = parensIf (p > 0) $ go 1 a ++ " → " ++ go 0 b
    go p (TyForall a t) = parensIf (p > 0) $ "∀" ++ a ++ ". " ++ go 0 t
    go _ (TyProd a b) = "(" ++ go 0 a ++ " × " ++ go 0 b ++ ")"
    go _ (TySum a b) = "(" ++ go 0 a ++ " + " ++ go 0 b ++ ")"

    parensIf True s = "(" ++ s ++ ")"
    parensIf False s = s

-- | Pretty print a term
prettyTerm :: Term -> String
prettyTerm = go 0
  where
    go :: Int -> Term -> String
    go _ (Var x) = x
    go p (Lam x e) = parensIf (p > 0) $ "λ" ++ x ++ ". " ++ go 0 e
    go p (LamAnn x t e) = parensIf (p > 0) $
      "λ(" ++ x ++ " : " ++ prettyType t ++ "). " ++ go 0 e
    go p (App e1 e2) = parensIf (p > 10) $ go 10 e1 ++ " " ++ go 11 e2
    go _ (Ann e t) = "(" ++ go 0 e ++ " : " ++ prettyType t ++ ")"
    go p (Let x e1 e2) = parensIf (p > 0) $
      "let " ++ x ++ " = " ++ go 0 e1 ++ " in " ++ go 0 e2
    go _ TmTrue = "true"
    go _ TmFalse = "false"
    go p (If c t f) = parensIf (p > 0) $
      "if " ++ go 0 c ++ " then " ++ go 0 t ++ " else " ++ go 0 f
    go _ Zero = "zero"
    go p (Suc n) = parensIf (p > 10) $ "suc " ++ go 11 n
    go p (NatRec z s n) = parensIf (p > 10) $
      "natrec " ++ go 11 z ++ " " ++ go 11 s ++ " " ++ go 11 n
    go _ TmUnit = "unit"
    go _ (Pair e1 e2) = "(" ++ go 0 e1 ++ ", " ++ go 0 e2 ++ ")"
    go p (Fst e) = parensIf (p > 10) $ "fst " ++ go 11 e
    go p (Snd e) = parensIf (p > 10) $ "snd " ++ go 11 e
    go p (Inl e) = parensIf (p > 10) $ "inl " ++ go 11 e
    go p (Inr e) = parensIf (p > 10) $ "inr " ++ go 11 e
    go p (Case s x1 e1 x2 e2) = parensIf (p > 0) $
      "case " ++ go 0 s ++ " of inl " ++ x1 ++ " → " ++ go 0 e1 ++
      " | inr " ++ x2 ++ " → " ++ go 0 e2
    go p (TyLam a e) = parensIf (p > 0) $ "Λ" ++ a ++ ". " ++ go 0 e
    go p (TyApp e t) = parensIf (p > 10) $ go 10 e ++ " [" ++ prettyType t ++ "]"

    parensIf True s = "(" ++ s ++ ")"
    parensIf False s = s

-- | Pretty print a value
prettyVal :: Val -> String
prettyVal (VBool True) = "true"
prettyVal (VBool False) = "false"
prettyVal (VNat n) = show n
prettyVal VUnit = "unit"
prettyVal (VPair v1 v2) = "(" ++ prettyVal v1 ++ ", " ++ prettyVal v2 ++ ")"
prettyVal (VInl v) = "inl " ++ prettyVal v
prettyVal (VInr v) = "inr " ++ prettyVal v
prettyVal (VLam x _) = "<λ" ++ x ++ ". ...>"
prettyVal (VTyLam a _) = "<Λ" ++ a ++ ". ...>"
prettyVal (VNeutral _) = "<neutral>"
