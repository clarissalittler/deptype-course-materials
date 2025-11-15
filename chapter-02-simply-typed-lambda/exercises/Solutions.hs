{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import TypeCheck
import Eval
import qualified Data.Map as Map

-- =============================================================================
-- Helper: Create natural number from Int
-- =============================================================================

natFromInt :: Int -> Term
natFromInt 0 = TmZero
natFromInt n = TmSucc (natFromInt (n - 1))

-- =============================================================================
-- Exercise 1: Arithmetic Operations (Easy)
-- =============================================================================

-- Exercise 1a: Addition
-- add m n = if iszero m then n else succ (add (pred m) n)
addNat :: Term -> Term -> Term
addNat m n = TmIf (TmIsZero m) n (TmSucc (addNat (TmPred m) n))

-- Helper: Create an addition function as a lambda term
-- λm:Nat. λn:Nat. <recursive addition>
-- Since STLC doesn't have fix, we'll use direct recursion for small examples
exampleAdd :: Term
exampleAdd = Lam "m" TyNat $ Lam "n" TyNat $
  TmIf (TmIsZero (Var "m"))
       (Var "n")
       (TmSucc (App (App exampleAdd (TmPred (Var "m"))) (Var "n")))

-- Exercise 1b: Multiplication by repeated addition
-- mult m n = if iszero m then 0 else add n (mult (pred m) n)
multNat :: Term -> Term -> Term
multNat m n = TmIf (TmIsZero m) TmZero (addNat n (multNat (TmPred m) n))

-- Exercise 1c: Less than
-- lt m n = if iszero m then (not (iszero n)) else (if iszero n then false else lt (pred m) (pred n))
ltNat :: Term -> Term -> Term
ltNat m n = TmIf (TmIsZero m)
                 (TmIf (TmIsZero n) TmFalse TmTrue)
                 (TmIf (TmIsZero n) TmFalse (ltNat (TmPred m) (TmPred n)))

-- Exercise 1d: Equality
-- eq m n = if iszero m then iszero n else (if iszero n then false else eq (pred m) (pred n))
eqNat :: Term -> Term -> Term
eqNat m n = TmIf (TmIsZero m)
                 (TmIsZero n)
                 (TmIf (TmIsZero n) TmFalse (eqNat (TmPred m) (TmPred n)))

-- =============================================================================
-- Exercise 2: Boolean Operations (Easy)
-- =============================================================================

-- Exercise 2a: AND
-- and = λb1:Bool. λb2:Bool. if b1 then b2 else false
boolAnd :: Term
boolAnd = Lam "b1" TyBool $ Lam "b2" TyBool $
  TmIf (Var "b1") (Var "b2") TmFalse

-- Exercise 2b: OR
-- or = λb1:Bool. λb2:Bool. if b1 then true else b2
boolOr :: Term
boolOr = Lam "b1" TyBool $ Lam "b2" TyBool $
  TmIf (Var "b1") TmTrue (Var "b2")

-- Exercise 2c: NOT
-- not = λb:Bool. if b then false else true
boolNot :: Term
boolNot = Lam "b" TyBool $
  TmIf (Var "b") TmFalse TmTrue

-- Exercise 2d: XOR
-- xor = λb1:Bool. λb2:Bool. if b1 then (not b2) else b2
boolXor :: Term
boolXor = Lam "b1" TyBool $ Lam "b2" TyBool $
  TmIf (Var "b1") (App boolNot (Var "b2")) (Var "b2")

-- =============================================================================
-- Exercise 3: Higher-Order Functions (Medium)
-- =============================================================================

-- Exercise 3a: Function composition
-- compose : (Nat → Nat) → (Nat → Nat) → Nat → Nat
-- compose = λf:Nat→Nat. λg:Nat→Nat. λx:Nat. f (g x)
compose :: Term
compose = Lam "f" (TyArr TyNat TyNat) $
          Lam "g" (TyArr TyNat TyNat) $
          Lam "x" TyNat $
          App (Var "f") (App (Var "g") (Var "x"))

-- Exercise 3b: Twice (apply function twice)
-- twice : (Nat → Nat) → Nat → Nat
-- twice = λf:Nat→Nat. λx:Nat. f (f x)
twice :: Term
twice = Lam "f" (TyArr TyNat TyNat) $
        Lam "x" TyNat $
        App (Var "f") (App (Var "f") (Var "x"))

-- Exercise 3c: Const (constant function)
-- const : Nat → Nat → Nat
-- const = λx:Nat. λy:Nat. x
constFn :: Term
constFn = Lam "x" TyNat $ Lam "y" TyNat $ Var "x"

-- Exercise 3d: Flip arguments
-- flip : (Nat → Nat → Nat) → Nat → Nat → Nat
-- flip = λf:Nat→Nat→Nat. λx:Nat. λy:Nat. f y x
flipFn :: Term
flipFn = Lam "f" (TyArr TyNat (TyArr TyNat TyNat)) $
         Lam "x" TyNat $
         Lam "y" TyNat $
         App (App (Var "f") (Var "y")) (Var "x")

-- =============================================================================
-- Exercise 4: Conditional Expressions (Medium)
-- =============================================================================

-- Exercise 4a: Max of two numbers
-- max = λm:Nat. λn:Nat. if lt m n then n else m
maxNat :: Term
maxNat = Lam "m" TyNat $ Lam "n" TyNat $
  TmIf (ltNat (Var "m") (Var "n")) (Var "n") (Var "m")

-- Exercise 4b: Min of two numbers
minNat :: Term
minNat = Lam "m" TyNat $ Lam "n" TyNat $
  TmIf (ltNat (Var "m") (Var "n")) (Var "m") (Var "n")

-- Exercise 4c: Absolute difference
-- absDiff = λm:Nat. λn:Nat. if lt m n then sub n m else sub m n
absDiff :: Term
absDiff = Lam "m" TyNat $ Lam "n" TyNat $
  TmIf (ltNat (Var "m") (Var "n"))
       (subNat (Var "n") (Var "m"))
       (subNat (Var "m") (Var "n"))
  where
    subNat x y = TmIf (TmIsZero y) x (subNat (TmPred x) (TmPred y))

-- =============================================================================
-- Exercise 5: Let Bindings as Syntactic Sugar (Medium)
-- =============================================================================

-- Exercise 5a: Simple let desugaring
-- let x = t1 in t2  ≡  (λx:τ. t2) t1
desugarLet :: Var -> Term -> Type -> Term -> Term
desugarLet x t1 ty t2 = App (Lam x ty t2) t1

-- Exercise 5b: Example using let
-- let x = 2 in let y = 3 in add x y
exampleLet :: Term
exampleLet =
  desugarLet "x" (natFromInt 2) TyNat $
  desugarLet "y" (natFromInt 3) TyNat $
  addNat (Var "x") (Var "y")

-- Exercise 5c: Multiple bindings
-- let x = 3 in let y = 4 in let z = 5 in add x (add y z)
exampleLetMultiple :: Term
exampleLetMultiple =
  desugarLet "x" (natFromInt 3) TyNat $
  desugarLet "y" (natFromInt 4) TyNat $
  desugarLet "z" (natFromInt 5) TyNat $
  addNat (Var "x") (addNat (Var "y") (Var "z"))

-- =============================================================================
-- Exercise 6: Type Safety Demonstrations (Hard)
-- =============================================================================

-- Exercise 6a: Progress theorem demonstration
data ProgressResult = IsValue | CanStep Term | Stuck
  deriving (Eq, Show)

demonstrateProgress :: Term -> ProgressResult
demonstrateProgress t
  | isValue t = IsValue
  | otherwise = case step t of
      Just t' -> CanStep t'
      Nothing -> Stuck

-- Exercise 6b: Preservation demonstration
-- If t : τ and t → t', then t' : τ
demonstratePreservation :: TypeContext -> Term -> Type -> Bool
demonstratePreservation ctx t ty =
  case (typeOf ctx t, step t) of
    (Right ty1, Just t') ->
      case typeOf ctx t' of
        Right ty2 -> ty1 == ty && ty2 == ty && ty1 == ty2
        Left _ -> False
    (Right _, Nothing) -> True  -- Already a value
    _ -> False

-- Exercise 6c: Type checking examples
wellTypedExamples :: [(String, Term, Type)]
wellTypedExamples =
  [ ("constant 5", natFromInt 5, TyNat)
  , ("true", TmTrue, TyBool)
  , ("identity on Nat", Lam "x" TyNat (Var "x"), TyArr TyNat TyNat)
  , ("succ function", Lam "x" TyNat (TmSucc (Var "x")), TyArr TyNat TyNat)
  , ("and function", boolAnd, TyArr TyBool (TyArr TyBool TyBool))
  ]

-- =============================================================================
-- Exercise 7: Advanced Examples (Hard)
-- =============================================================================

-- Exercise 7a: Factorial-like function (limited by lack of general recursion)
-- fact3 = λn:Nat. if iszero n then 1 else if iszero (pred n) then 1 else if iszero (pred (pred n)) then 2 else 6
fact3 :: Term
fact3 = Lam "n" TyNat $
  TmIf (TmIsZero (Var "n"))
       (natFromInt 1)
       (TmIf (TmIsZero (TmPred (Var "n")))
             (natFromInt 1)
             (TmIf (TmIsZero (TmPred (TmPred (Var "n"))))
                   (natFromInt 2)
                   (natFromInt 6)))

-- Exercise 7b: Conditional chains
-- sign = λn:Nat. if iszero n then 0 else 1
sign :: Term
sign = Lam "n" TyNat $
  TmIf (TmIsZero (Var "n")) TmZero (natFromInt 1)

-- Exercise 7c: Boolean to Nat conversion
-- boolToNat = λb:Bool. if b then 1 else 0
boolToNat :: Term
boolToNat = Lam "b" TyBool $
  TmIf (Var "b") (natFromInt 1) TmZero

-- Exercise 7d: Complex conditional
-- isEven2 = λn:Nat. if iszero n then true else if iszero (pred n) then false else iszero (pred (pred n))
-- (works for 0, 1, 2 only due to no recursion)
isEven2 :: Term
isEven2 = Lam "n" TyNat $
  TmIf (TmIsZero (Var "n"))
       TmTrue
       (TmIf (TmIsZero (TmPred (Var "n")))
             TmFalse
             (TmIsZero (TmPred (TmPred (Var "n")))))

-- =============================================================================
-- Example Programs
-- =============================================================================

-- Example 1: Compute 3 + 4
example1 :: Term
example1 = addNat (natFromInt 3) (natFromInt 4)

-- Example 2: Test 5 == 5
example2 :: Term
example2 = eqNat (natFromInt 5) (natFromInt 5)

-- Example 3: Test 3 < 5
example3 :: Term
example3 = ltNat (natFromInt 3) (natFromInt 5)

-- Example 4: Max of 3 and 5
example4 :: Term
example4 = App (App maxNat (natFromInt 3)) (natFromInt 5)

-- Example 5: Twice succ applied to 3 = 5
example5 :: Term
example5 = App (App twice (Lam "x" TyNat (TmSucc (Var "x")))) (natFromInt 3)

-- Example 6: Boolean operations
example6 :: Term
example6 = App (App boolAnd TmTrue) TmFalse

-- Example 7: Composition
-- (succ ∘ succ) 3 = 5
example7 :: Term
example7 = App (App (App compose
                        (Lam "x" TyNat (TmSucc (Var "x"))))
                    (Lam "x" TyNat (TmSucc (Var "x"))))
              (natFromInt 3)
