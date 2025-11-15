{-# LANGUAGE LambdaCase #-}

module Pretty
  ( prettyKind, prettyType, prettyTerm
  ) where

import Syntax

-- | Pretty-print a kind
prettyKind :: Kind -> String
prettyKind = go False
  where
    go _ KStar = "*"
    go needParens (KArr k1 k2) =
      let s = go True k1 ++ " → " ++ go False k2
      in if needParens then "(" ++ s ++ ")" else s

-- | Pretty-print a type
prettyType :: Type -> String
prettyType = go 0
  where
    -- Precedence levels:
    -- 0: top level (no parens needed)
    -- 1: arrow right side
    -- 2: application left side
    -- 3: application right side

    go :: Int -> Type -> String
    go _ (TyVar a) = a
    go prec (TyArr t1 t2) =
      let s = go 2 t1 ++ " → " ++ go 1 t2
      in if prec > 1 then "(" ++ s ++ ")" else s
    go prec (TyForall a k t) =
      let s = "∀" ++ a ++ "::" ++ prettyKind k ++ ". " ++ go 0 t
      in if prec > 0 then "(" ++ s ++ ")" else s
    go prec (TyLam a k t) =
      let s = "λ" ++ a ++ "::" ++ prettyKind k ++ ". " ++ go 0 t
      in if prec > 0 then "(" ++ s ++ ")" else s
    go prec (TyApp t1 t2) =
      let s = go 2 t1 ++ " " ++ go 3 t2
      in if prec > 2 then "(" ++ s ++ ")" else s
    go _ TyBool = "Bool"
    go _ TyNat = "Nat"

-- | Pretty-print a term
prettyTerm :: Term -> String
prettyTerm = go 0
  where
    -- Precedence levels:
    -- 0: top level
    -- 1: application left side
    -- 2: application right side

    go :: Int -> Term -> String
    go _ (Var x) = x
    go prec (Lam x ty t) =
      let s = "λ(" ++ x ++ ":" ++ prettyType ty ++ "). " ++ go 0 t
      in if prec > 0 then "(" ++ s ++ ")" else s
    go prec (App t1 t2) =
      let s = go 1 t1 ++ " " ++ go 2 t2
      in if prec > 1 then "(" ++ s ++ ")" else s
    go prec (TyAbs a k t) =
      let s = "Λ" ++ a ++ "::" ++ prettyKind k ++ ". " ++ go 0 t
      in if prec > 0 then "(" ++ s ++ ")" else s
    go prec (TyAppTerm t ty) =
      let s = go 1 t ++ " [" ++ prettyType ty ++ "]"
      in if prec > 1 then "(" ++ s ++ ")" else s
    go _ TmTrue = "true"
    go _ TmFalse = "false"
    go prec (TmIf t1 t2 t3) =
      let s = "if " ++ go 0 t1 ++ " then " ++ go 0 t2 ++ " else " ++ go 0 t3
      in if prec > 0 then "(" ++ s ++ ")" else s
    go _ TmZero = "0"
    go prec (TmSucc t) =
      case toNat t of
        Just n -> show (n + 1)
        Nothing ->
          let s = "succ " ++ go 2 t
          in if prec > 1 then "(" ++ s ++ ")" else s
    go prec (TmPred t) =
      let s = "pred " ++ go 2 t
      in if prec > 1 then "(" ++ s ++ ")" else s
    go prec (TmIsZero t) =
      let s = "iszero " ++ go 2 t
      in if prec > 1 then "(" ++ s ++ ")" else s

    -- Try to convert a term to a natural number
    toNat :: Term -> Maybe Int
    toNat TmZero = Just 0
    toNat (TmSucc t) = (+ 1) <$> toNat t
    toNat _ = Nothing
