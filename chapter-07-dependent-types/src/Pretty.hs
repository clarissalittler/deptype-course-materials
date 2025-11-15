{-# LANGUAGE LambdaCase #-}

module Pretty
  ( pretty
  ) where

import Syntax
import qualified Data.Set as Set

-- | Pretty-print a term
pretty :: Term -> String
pretty = go 0
  where
    -- Precedence levels:
    -- 0: top level
    -- 1: application left side
    -- 2: application right side / atom

    go :: Int -> Term -> String
    go _ Type = "Type"
    go _ (Var x) = x

    go prec (Lam x ty t) =
      let s = "λ(" ++ x ++ ":" ++ go 0 ty ++ "). " ++ go 0 t
      in if prec > 0 then "(" ++ s ++ ")" else s

    go prec (App t1 t2) =
      let s = go 1 t1 ++ " " ++ go 2 t2
      in if prec > 1 then "(" ++ s ++ ")" else s

    go prec (Pi x a b) =
      let s = if x `elem` freeVarsList b
              then "Π(" ++ x ++ ":" ++ go 0 a ++ "). " ++ go 0 b
              else go 0 a ++ " → " ++ go 0 b
      in if prec > 0 then "(" ++ s ++ ")" else s

    go prec (Sigma x a b) =
      let s = "Σ(" ++ x ++ ":" ++ go 0 a ++ "). " ++ go 0 b
      in if prec > 0 then "(" ++ s ++ ")" else s

    go prec (Pair t1 t2) =
      let s = "(" ++ go 0 t1 ++ ", " ++ go 0 t2 ++ ")"
      in if prec > 1 then "(" ++ s ++ ")" else s

    go prec (Fst t) =
      let s = "fst " ++ go 2 t
      in if prec > 1 then "(" ++ s ++ ")" else s

    go prec (Snd t) =
      let s = "snd " ++ go 2 t
      in if prec > 1 then "(" ++ s ++ ")" else s

    go _ Nat = "Nat"
    go _ Zero = "0"
    go prec (Succ t) = case toNat t of
      Just n -> show (n + 1)
      Nothing ->
        let s = "succ " ++ go 2 t
        in if prec > 1 then "(" ++ s ++ ")" else s

    go _ Bool = "Bool"
    go _ TmTrue = "true"
    go _ TmFalse = "false"

    go prec (If t1 t2 t3) =
      let s = "if " ++ go 0 t1 ++ " then " ++ go 0 t2 ++ " else " ++ go 0 t3
      in if prec > 0 then "(" ++ s ++ ")" else s

    -- Helper: convert a term to a natural number if possible
    toNat :: Term -> Maybe Int
    toNat Zero = Just 0
    toNat (Succ t) = (+ 1) <$> toNat t
    toNat _ = Nothing

    -- Helper: get free variables as a list
    freeVarsList :: Term -> [Name]
    freeVarsList = Set.toList . freeVars
