-- | Pretty printer for NbE

module Pretty
  ( prettyTerm
  , prettyNf
  , prettyNe
  , prettyVal
  ) where

import Syntax
import Semantic

-- | Pretty print a term
prettyTerm :: [String] -> Term -> String
prettyTerm names = go 0
  where
    lookupName i = if i < length names then names !! i else "?" ++ show i

    go :: Int -> Term -> String
    go _ (TVar i) = lookupName i
    go p (TLam x t) = parensIf (p > 0) $ "λ" ++ x ++ ". " ++ go 0 t
    go p (TApp t u) = parensIf (p > 10) $ go 10 t ++ " " ++ go 11 u
    go p (TPi x a b) = parensIf (p > 0) $
      "(" ++ x ++ " : " ++ go 0 a ++ ") → " ++ go 0 b
    go _ TU = "Type"
    go p (TLet x a t u) = parensIf (p > 0) $
      "let " ++ x ++ " : " ++ go 0 a ++ " = " ++ go 0 t ++ " in " ++ go 0 u
    go _ TBool = "Bool"
    go _ TTrue = "true"
    go _ TFalse = "false"
    go p (TIf b t f) = parensIf (p > 0) $
      "if " ++ go 0 b ++ " then " ++ go 0 t ++ " else " ++ go 0 f
    go _ TNat = "Nat"
    go _ TZero = "zero"
    go p (TSuc n) = parensIf (p > 10) $ "suc " ++ go 11 n
    go p (TNatElim _ z s n) = parensIf (p > 10) $
      "natElim ... " ++ go 11 z ++ " " ++ go 11 s ++ " " ++ go 11 n

    parensIf True s = "(" ++ s ++ ")"
    parensIf False s = s

-- | Pretty print a normal form
prettyNf :: Int -> Nf -> String
prettyNf l = go 0
  where
    name i = "x" ++ show (l - i - 1)

    go :: Int -> Nf -> String
    go _ (NfNe ne) = prettyNe' l ne
    go p (NfLam x nf) = parensIf (p > 0) $ "λ" ++ x ++ ". " ++ prettyNf (l+1) nf
    go p (NfPi x a b) = parensIf (p > 0) $
      "(" ++ x ++ " : " ++ go 0 a ++ ") → " ++ prettyNf (l+1) b
    go _ NfU = "Type"
    go _ NfBool = "Bool"
    go _ NfTrue = "true"
    go _ NfFalse = "false"
    go _ NfNat = "Nat"
    go _ NfZero = "zero"
    go p (NfSuc n) = parensIf (p > 10) $ "suc " ++ go 11 n

    parensIf True s = "(" ++ s ++ ")"
    parensIf False s = s

-- | Pretty print a neutral
prettyNe' :: Int -> Ne -> String
prettyNe' l = go 0
  where
    name i = "x" ++ show i

    go :: Int -> Ne -> String
    go _ (NeVar i) = name i
    go p (NeApp ne nf) = parensIf (p > 10) $ go 10 ne ++ " " ++ prettyNf l nf
    go p (NeIf ne t f) = parensIf (p > 0) $
      "if " ++ go 0 ne ++ " then " ++ prettyNf l t ++ " else " ++ prettyNf l f
    go p (NeNatElim _ z s ne) = parensIf (p > 10) $
      "natElim ... " ++ prettyNf l z ++ " " ++ prettyNf l s ++ " " ++ go 11 ne

    parensIf True s = "(" ++ s ++ ")"
    parensIf False s = s

prettyNe :: Int -> Ne -> String
prettyNe = prettyNe'

-- | Pretty print a semantic value (for debugging)
prettyVal :: Int -> Val -> String
prettyVal l v = prettyNf l (quote l v)
  where
    quote :: Int -> Val -> Nf
    quote = undefined  -- Would need to import from NbE
