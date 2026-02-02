{-# LANGUAGE LambdaCase #-}

module Pretty
  ( pretty
  , prettyPattern
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
    go _ (Universe i) = "Type" ++ if i == 0 then "" else show i
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

    go _ (Ind name) = name

    go _ (Con name []) = name
    go prec (Con name args) =
      let s = name ++ " " ++ unwords (map (go 2) args)
      in if prec > 1 then "(" ++ s ++ ")" else s

    go prec (Match t branches) =
      let s = "match " ++ go 0 t ++ " with " ++
              unwords ["|" ++ prettyPattern pat ++ " -> " ++ go 0 rhs | (pat, rhs) <- branches]
      in if prec > 0 then "(" ++ s ++ ")" else s

    go prec (Eq a x y) =
      let s = "Eq " ++ go 2 a ++ " " ++ go 2 x ++ " " ++ go 2 y
      in if prec > 1 then "(" ++ s ++ ")" else s

    go prec (Refl x) =
      let s = "refl " ++ go 2 x
      in if prec > 1 then "(" ++ s ++ ")" else s

    go prec (J a c p x y eq) =
      let s = "J(" ++ go 0 a ++ ", " ++ go 0 c ++ ", " ++ go 0 p ++ ", " ++
              go 0 x ++ ", " ++ go 0 y ++ ", " ++ go 0 eq ++ ")"
      in if prec > 1 then "(" ++ s ++ ")" else s

    go _ Nat = "Nat"
    go _ Zero = "0"
    go prec (Succ t) = case toNat t of
      Just n -> show (n + 1)
      Nothing ->
        let s = "succ " ++ go 2 t
        in if prec > 1 then "(" ++ s ++ ")" else s

    go prec (NatElim p z s n) =
      let str = "natElim(" ++ go 0 p ++ ", " ++ go 0 z ++ ", " ++ go 0 s ++ ", " ++ go 0 n ++ ")"
      in if prec > 1 then "(" ++ str ++ ")" else str

    go _ Bool = "Bool"
    go _ TmTrue = "true"
    go _ TmFalse = "false"

    go prec (BoolElim p t f b) =
      let str = "boolElim(" ++ go 0 p ++ ", " ++ go 0 t ++ ", " ++ go 0 f ++ ", " ++ go 0 b ++ ")"
      in if prec > 1 then "(" ++ str ++ ")" else str

    go _ Unit = "Unit"
    go _ TT = "TT"

    go prec (UnitElim p u x) =
      let str = "unitElim(" ++ go 0 p ++ ", " ++ go 0 u ++ ", " ++ go 0 x ++ ")"
      in if prec > 1 then "(" ++ str ++ ")" else str

    go _ Empty = "Empty"

    go prec (EmptyElim p e) =
      let str = "emptyElim(" ++ go 0 p ++ ", " ++ go 0 e ++ ")"
      in if prec > 1 then "(" ++ str ++ ")" else str

    -- Helper: convert a term to a natural number if possible
    toNat :: Term -> Maybe Int
    toNat Zero = Just 0
    toNat (Succ t) = (+ 1) <$> toNat t
    toNat _ = Nothing

    -- Helper: get free variables as a list
    freeVarsList :: Term -> [Name]
    freeVarsList = Set.toList . freeVars

-- | Pretty-print a pattern
prettyPattern :: Pattern -> String
prettyPattern = \case
  PVar x -> x
  PWild -> "_"
  PCon name [] -> name
  PCon name args -> name ++ " " ++ unwords (map prettyPatternAtom args)

prettyPatternAtom :: Pattern -> String
prettyPatternAtom p@(PCon _ (_:_)) = "(" ++ prettyPattern p ++ ")"
prettyPatternAtom p = prettyPattern p
