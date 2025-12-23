-- | Pretty printing for denotational semantics

module Pretty
  ( prettyTerm
  , prettyType
  , prettyDom
  ) where

import Syntax
import Domain

-- | Pretty print a type
prettyType :: Type -> String
prettyType = go 0
  where
    go :: Int -> Type -> String
    go _ TyBool = "Bool"
    go _ TyNat = "Nat"
    go _ TyUnit = "Unit"
    go p (TyArr a b) = parensIf (p > 0) $ go 1 a ++ " → " ++ go 0 b

    parensIf True s = "(" ++ s ++ ")"
    parensIf False s = s

-- | Pretty print a term
prettyTerm :: Term -> String
prettyTerm = go 0
  where
    go :: Int -> Term -> String
    go _ (Var x) = x
    go p (Lam x t e) = parensIf (p > 0) $
      "λ(" ++ x ++ " : " ++ prettyType t ++ "). " ++ go 0 e
    go p (App e1 e2) = parensIf (p > 10) $ go 10 e1 ++ " " ++ go 11 e2
    go p (Let x e1 e2) = parensIf (p > 0) $
      "let " ++ x ++ " = " ++ go 0 e1 ++ " in " ++ go 0 e2
    go p (Fix e) = parensIf (p > 10) $ "fix " ++ go 11 e
    go _ TmTrue = "true"
    go _ TmFalse = "false"
    go p (If c t f) = parensIf (p > 0) $
      "if " ++ go 0 c ++ " then " ++ go 0 t ++ " else " ++ go 0 f
    go _ Zero = "0"
    go p (Suc n) = parensIf (p > 10) $ "suc " ++ go 11 n
    go p (Pred n) = parensIf (p > 10) $ "pred " ++ go 11 n
    go p (IsZero n) = parensIf (p > 10) $ "iszero " ++ go 11 n
    go p (NatRec z s n) = parensIf (p > 10) $
      "natrec " ++ go 11 z ++ " " ++ go 11 s ++ " " ++ go 11 n
    go _ TmUnit = "()"
    go _ (Bottom t) = "⊥:" ++ prettyType t

    parensIf True s = "(" ++ s ++ ")"
    parensIf False s = s

-- | Pretty print a domain value
prettyDom :: Dom -> String
prettyDom DBottom = "⊥"
prettyDom (DBool True) = "true"
prettyDom (DBool False) = "false"
prettyDom (DNat n) = show n
prettyDom DUnit = "()"
prettyDom (DFun _) = "<function>"
