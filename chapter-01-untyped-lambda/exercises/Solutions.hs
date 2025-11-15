module Solutions where

import Syntax
import Eval

-- | Helper to create lambda abstractions more easily
lam :: Var -> Term -> Term
lam = Lam

lam2 :: Var -> Var -> Term -> Term
lam2 x y body = lam x (lam y body)

lam3 :: Var -> Var -> Var -> Term -> Term
lam3 x y z body = lam x (lam y (lam z body))

-- =============================================================================
-- Exercise 1: Church Boolean Operations (Easy)
-- =============================================================================

-- | Church encoding for true: λt. λf. t
-- Selects the first argument
churchTrue :: Term
churchTrue = lam2 "t" "f" (Var "t")

-- | Church encoding for false: λt. λf. f
-- Selects the second argument
churchFalse :: Term
churchFalse = lam2 "t" "f" (Var "f")

-- | Exercise 1a: AND operation
-- and = λp. λq. p q false
-- If p is true, return q; otherwise return false
churchAnd :: Term
churchAnd = lam2 "p" "q" $
  App (App (Var "p") (Var "q")) churchFalse

-- | Exercise 1b: OR operation
-- or = λp. λq. p true q
-- If p is true, return true; otherwise return q
churchOr :: Term
churchOr = lam2 "p" "q" $
  App (App (Var "p") churchTrue) (Var "q")

-- | Exercise 1c: XOR operation
-- xor = λp. λq. p (not q) q
-- If p is true, return (not q); otherwise return q
-- First we need NOT:
-- not = λp. p false true
churchNot :: Term
churchNot = lam "p" $
  App (App (Var "p") churchFalse) churchTrue

churchXor :: Term
churchXor = lam2 "p" "q" $
  App (App (Var "p") (App churchNot (Var "q"))) (Var "q")

-- =============================================================================
-- Exercise 2: Church Numeral Arithmetic (Medium)
-- =============================================================================

-- | Church numerals: n = λf. λx. f^n x
-- 0 = λf. λx. x
-- 1 = λf. λx. f x
-- 2 = λf. λx. f (f x)
-- etc.

churchZero :: Term
churchZero = lam2 "f" "x" (Var "x")

churchOne :: Term
churchOne = lam2 "f" "x" (App (Var "f") (Var "x"))

churchTwo :: Term
churchTwo = lam2 "f" "x" (App (Var "f") (App (Var "f") (Var "x")))

churchThree :: Term
churchThree = lam2 "f" "x" (App (Var "f") (App (Var "f") (App (Var "f") (Var "x"))))

-- | Successor: λn. λf. λx. f (n f x)
churchSucc :: Term
churchSucc = lam3 "n" "f" "x" $
  App (Var "f") (App (App (Var "n") (Var "f")) (Var "x"))

-- | Addition: λm. λn. λf. λx. m f (n f x)
churchPlus :: Term
churchPlus = lam2 "m" "n" $ lam2 "f" "x" $
  App (App (Var "m") (Var "f"))
      (App (App (Var "n") (Var "f")) (Var "x"))

-- | Multiplication: λm. λn. λf. m (n f)
churchMult :: Term
churchMult = lam2 "m" "n" $ lam "f" $
  App (Var "m") (App (Var "n") (Var "f"))

-- | Church pairs for implementing predecessor
-- pair = λx. λy. λf. f x y
-- fst = λp. p (λx. λy. x)
-- snd = λp. p (λx. λy. y)

churchPair :: Term
churchPair = lam3 "x" "y" "f" $
  App (App (Var "f") (Var "x")) (Var "y")

churchFst :: Term
churchFst = lam "p" $
  App (Var "p") (lam2 "x" "y" (Var "x"))

churchSnd :: Term
churchSnd = lam "p" $
  App (Var "p") (lam2 "x" "y" (Var "y"))

-- | Exercise 2a: Predecessor
-- The trick: iterate from (0, 0) to (n-1, n) using pairs
-- pred = λn. fst (n (λp. pair (snd p) (succ (snd p))) (pair 0 0))
-- Simpler version:
-- pred = λn. λf. λx. n (λg. λh. h (g f)) (λu. x) (λu. u)
churchPred :: Term
churchPred = lam3 "n" "f" "x" $
  App (App (App (Var "n")
                (lam2 "g" "h" $
                  App (Var "h") (App (Var "g") (Var "f"))))
           (lam "u" (Var "x")))
      (lam "u" (Var "u"))

-- | Exercise 2b: Subtraction
-- sub = λm. λn. n pred m
-- Apply pred n times to m
churchSub :: Term
churchSub = lam2 "m" "n" $
  App (App (Var "n") churchPred) (Var "m")

-- | Helper: isZero test
-- isZero = λn. n (λx. false) true
churchIsZero :: Term
churchIsZero = lam "n" $
  App (App (Var "n") (lam "x" churchFalse)) churchTrue

-- | Exercise 2c: Equality test
-- isEqual = λm. λn. and (isZero (sub m n)) (isZero (sub n m))
churchIsEqual :: Term
churchIsEqual = lam2 "m" "n" $
  App (App churchAnd
           (App churchIsZero (App (App churchSub (Var "m")) (Var "n"))))
      (App churchIsZero (App (App churchSub (Var "n")) (Var "m")))

-- =============================================================================
-- Exercise 3: Recursion and Fixed Points (Hard)
-- =============================================================================

-- | Exercise 3a: Y Combinator (for normal-order evaluation)
-- Y = λf. (λx. f (x x)) (λx. f (x x))
-- This diverges under call-by-value!
yCombinator :: Term
yCombinator = lam "f" $
  App (lam "x" $ App (Var "f") (App (Var "x") (Var "x")))
      (lam "x" $ App (Var "f") (App (Var "x") (Var "x")))

-- | Z Combinator (for call-by-value evaluation)
-- Z = λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))
zCombinator :: Term
zCombinator = lam "f" $
  App (lam "x" $ App (Var "f") (lam "y" $ App (App (Var "x") (Var "x")) (Var "y")))
      (lam "x" $ App (Var "f") (lam "y" $ App (App (Var "x") (Var "x")) (Var "y")))

-- | Exercise 3b: Factorial using Z combinator
-- factorial = Z (λf. λn. if (isZero n) 1 (mult n (f (pred n))))
-- Using Church encodings:
churchFactorial :: Term
churchFactorial = App zCombinator $
  lam2 "f" "n" $
    App (App (App churchIsZero (Var "n"))
             churchOne)  -- then branch
        (App (App churchMult (Var "n"))  -- else branch: n * f(pred n)
             (App (Var "f") (App churchPred (Var "n"))))

-- | Exercise 3c: Fibonacci
-- fibonacci = Z (λf. λn. if (isZero n) 0 (if (isZero (pred n)) 1 (plus (f (pred n)) (f (pred (pred n))))))
churchFibonacci :: Term
churchFibonacci = App zCombinator $
  lam2 "f" "n" $
    App (App (App churchIsZero (Var "n"))
             churchZero)  -- fib(0) = 0
        (App (App (App churchIsZero (App churchPred (Var "n")))
                  churchOne)  -- fib(1) = 1
             (App (App churchPlus  -- fib(n) = fib(n-1) + fib(n-2)
                       (App (Var "f") (App churchPred (Var "n"))))
                  (App (Var "f") (App churchPred (App churchPred (Var "n"))))))

-- =============================================================================
-- Exercise 4: Advanced Combinators (Hard)
-- =============================================================================

-- | Exercise 4a: SKI combinators
-- I combinator: I = λx. x
combI :: Term
combI = lam "x" (Var "x")

-- K combinator: K = λx. λy. x
combK :: Term
combK = lam2 "x" "y" (Var "x")

-- S combinator: S = λx. λy. λz. x z (y z)
combS :: Term
combS = lam3 "x" "y" "z" $
  App (App (Var "x") (Var "z"))
      (App (Var "y") (Var "z"))

-- | Exercise 4b: Omega (Ω)
-- ω = λx. x x
omega :: Term
omega = lam "x" (App (Var "x") (Var "x"))

-- Ω = ω ω
bigOmega :: Term
bigOmega = App omega omega

-- | Exercise 4c: I from S and K
-- I = S K K
-- Proof: S K K x = K x (K x) = x
iFromSK :: Term
iFromSK = App (App combS combK) combK

-- =============================================================================
-- Exercise 5: List Operations (Medium-Hard)
-- =============================================================================

-- | Church-encoded lists
-- nil = λc. λn. n
-- cons = λh. λt. λc. λn. c h (t c n)

churchNil :: Term
churchNil = lam2 "c" "n" (Var "n")

churchCons :: Term
churchCons = lam2 "h" "t" $ lam2 "c" "n" $
  App (App (Var "c") (Var "h"))
      (App (App (Var "t") (Var "c")) (Var "n"))

-- | Helper: create a list from elements
-- [1, 2, 3] = cons 1 (cons 2 (cons 3 nil))
makeChurchList :: [Term] -> Term
makeChurchList [] = churchNil
makeChurchList (x:xs) = App (App churchCons x) (makeChurchList xs)

-- | Exercise 5a: Length
-- length = λl. l (λh. λt. succ t) 0
-- For each element, increment the accumulator
churchLength :: Term
churchLength = lam "l" $
  App (App (Var "l")
           (lam2 "h" "t" $ App churchSucc (Var "t")))
      churchZero

-- | Exercise 5b: Map
-- map = λf. λl. l (λh. λt. cons (f h) t) nil
churchMap :: Term
churchMap = lam2 "f" "l" $
  App (App (Var "l")
           (lam2 "h" "t" $
             App (App churchCons (App (Var "f") (Var "h")))
                 (Var "t")))
      churchNil

-- | Exercise 5c: Filter
-- filter = λp. λl. l (λh. λt. p h (cons h t) t) nil
-- If predicate is true for h, cons h to result; otherwise skip h
churchFilter :: Term
churchFilter = lam2 "p" "l" $
  App (App (Var "l")
           (lam2 "h" "t" $
             App (App (App (Var "p") (Var "h"))
                      (App (App churchCons (Var "h")) (Var "t")))
                 (Var "t")))
      churchNil

-- | Exercise 5d: Fold
-- For Church-encoded lists, fold is trivial!
-- fold = λf. λz. λl. l f z
-- The list IS its own fold function!
churchFold :: Term
churchFold = lam3 "f" "z" "l" $
  App (App (Var "l") (Var "f")) (Var "z")

-- =============================================================================
-- Additional Challenges
-- =============================================================================

-- | Ackermann function
-- ack = Y (λa. λm. λn.
--   if (isZero m)
--     (succ n)
--     (if (isZero n)
--       (a (pred m) 1)
--       (a (pred m) (a m (pred n)))))
churchAckermann :: Term
churchAckermann = App zCombinator $
  lam3 "a" "m" "n" $
    App (App (App churchIsZero (Var "m"))
             (App churchSucc (Var "n")))  -- m = 0: return n + 1
        (App (App (App churchIsZero (Var "n"))
                  (App (App (Var "a") (App churchPred (Var "m"))) churchOne))  -- n = 0: a(m-1, 1)
             (App (App (Var "a") (App churchPred (Var "m")))  -- a(m-1, a(m, n-1))
                  (App (App (Var "a") (Var "m")) (App churchPred (Var "n")))))
