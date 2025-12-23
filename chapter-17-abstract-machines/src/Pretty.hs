-- | Pretty printer for abstract machine terms and values

module Pretty
  ( prettyTerm
  , prettyValue
  , prettyState
  ) where

import Syntax
import qualified CEK

-- | Pretty print a term
prettyTerm :: Term -> String
prettyTerm = go 0
  where
    go :: Int -> Term -> String
    go _ (TmVar x) = x
    go p (TmLam x t) = parensIf (p > 0) $ "λ" ++ x ++ ". " ++ go 0 t
    go p (TmApp t1 t2) = parensIf (p > 10) $ go 10 t1 ++ " " ++ go 11 t2
    go _ (TmInt n) = show n
    go p (TmAdd t1 t2) = parensIf (p > 6) $ go 6 t1 ++ " + " ++ go 7 t2
    go p (TmSub t1 t2) = parensIf (p > 6) $ go 6 t1 ++ " - " ++ go 7 t2
    go p (TmMul t1 t2) = parensIf (p > 7) $ go 7 t1 ++ " * " ++ go 8 t2
    go p (TmIf0 t1 t2 t3) = parensIf (p > 0) $
      "if0 " ++ go 0 t1 ++ " then " ++ go 0 t2 ++ " else " ++ go 0 t3
    go p (TmLet x t1 t2) = parensIf (p > 0) $
      "let " ++ x ++ " = " ++ go 0 t1 ++ " in " ++ go 0 t2
    go p (TmFix t) = parensIf (p > 10) $ "fix " ++ go 11 t

    parensIf True s = "(" ++ s ++ ")"
    parensIf False s = s

-- | Pretty print a value
prettyValue :: Value -> String
prettyValue (VInt n) = show n
prettyValue (VClosure x t _) = "<closure: λ" ++ x ++ ". " ++ prettyTerm t ++ ">"

-- | Pretty print CEK state
prettyState :: CEK.State -> String
prettyState (CEK.Eval t env k) =
  "Eval { term = " ++ prettyTerm t ++
  ", env = " ++ show (length env) ++ " bindings" ++
  ", kont = " ++ show (length k) ++ " frames }"
prettyState (CEK.Apply k v) =
  "Apply { kont = " ++ show (length k) ++ " frames" ++
  ", value = " ++ prettyValue v ++ " }"
