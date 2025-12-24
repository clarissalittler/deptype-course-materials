module Pretty
  ( pretty
  , prettyPrec
  ) where

import Syntax
import qualified Data.Set as Set
import Data.Set (Set)

-- | Pretty-print a term with precedence
-- Renames shadowed variables for clarity
prettyPrec :: Int -> Term -> String
prettyPrec p t = prettyPrecWith Set.empty p t

-- | Pretty-print with a set of variables already in scope
prettyPrecWith :: Set Var -> Int -> Term -> String
prettyPrecWith _ _ (Var x) = x
prettyPrecWith scope p (Lam x t) =
  parensIf (p > 0) $ "λ" ++ x' ++ binders ++ ". " ++ body
  where
    -- Rename x if it shadows a variable in scope
    x' = if x `Set.member` scope
         then freshVar x (scope `Set.union` freeVars t)
         else x
    -- Rename the body if we renamed the variable
    t' = if x' /= x then renameVar x x' t else t
    scope' = Set.insert x' scope
    -- Collect consecutive lambdas, renaming shadowed variables
    (binders, body) = collectLambdas scope' t'

    collectLambdas :: Set Var -> Term -> (String, String)
    collectLambdas sc (Lam y body') =
      let y' = if y `Set.member` sc
               then freshVar y (sc `Set.union` freeVars body')
               else y
          body'' = if y' /= y then renameVar y y' body' else body'
          sc' = Set.insert y' sc
          (rest, final) = collectLambdas sc' body''
      in (" " ++ y' ++ rest, final)
    collectLambdas sc other = ("", prettyPrecWith sc 0 other)

prettyPrecWith scope p (App t1 t2) =
  parensIf (p > 1) $ prettyPrecWith scope 1 t1 ++ " " ++ prettyPrecWith scope 2 t2

-- | Rename a bound variable in a term (simple renaming, not full substitution)
-- This is used when we need to rename a lambda parameter to avoid shadowing
renameVar :: Var -> Var -> Term -> Term
renameVar old new = go
  where
    go (Var x)
      | x == old  = Var new
      | otherwise = Var x
    go (Lam x body)
      | x == old  = Lam x body  -- old is shadowed, stop renaming
      | x == new  = -- new would be captured, need to rename this lambda first
          let x' = freshVar x (Set.insert new (freeVars body))
          in Lam x' (go (renameVar x x' body))
      | otherwise = Lam x (go body)
    go (App t1 t2) = App (go t1) (go t2)

-- | Pretty-print a term
pretty :: Term -> String
pretty = prettyPrec 0

-- | Add parentheses if condition is true
parensIf :: Bool -> String -> String
parensIf True s = "(" ++ s ++ ")"
parensIf False s = s
