module Pretty
  ( pretty
  , prettyPrec
  ) where

import Syntax

-- | Pretty-print a term with precedence
prettyPrec :: Int -> Term -> String
prettyPrec _ (Var x) = x
prettyPrec p (Lam x t) =
  parensIf (p > 0) $ "λ" ++ x ++ collectLambdas t
  where
    collectLambdas (Lam y t') = " " ++ y ++ collectLambdas t'
    collectLambdas t' = ". " ++ prettyPrec 0 t'
prettyPrec p (App t1 t2) =
  parensIf (p > 1) $ prettyPrec 1 t1 ++ " " ++ prettyPrec 2 t2

-- | Pretty-print a term
pretty :: Term -> String
pretty = prettyPrec 0

-- | Add parentheses if condition is true
parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s
