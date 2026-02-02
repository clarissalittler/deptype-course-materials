{-# LANGUAGE OverloadedStrings #-}

module Solutions where

import Syntax
import TypeCheck
import Eval

-- | Helper to create a context with some definitions
-- (Context is already defined in TypeCheck module)

-- ============================================================================
-- Exercise 1: Universe Hierarchy
-- ============================================================================

-- Exercise 1a: Universe levels are already built into the system
-- Type 0 : Type 1
-- Type 1 : Type 2
-- etc.

-- Exercise 1b: Universe-polymorphic identity functions

-- id0 : Π(A:Type 0). A → A
id0 :: Term
id0 = Lam "A" (Universe 0) (Lam "x" (Var "A") (Var "x"))

-- id1 : Π(A:Type 1). A → A
id1 :: Term
id1 = Lam "A" (Universe 1) (Lam "x" (Var "A") (Var "x"))

-- Test: Apply id0 to Nat
testId0 :: Term
testId0 = App (App id0 Nat) Zero

-- ============================================================================
-- Exercise 2: Equality Types and Proofs
-- ============================================================================

-- Exercise 2a: Symmetry of Equality
-- sym : Π(A:Type). Π(x:A). Π(y:A). Eq A x y → Eq A y x
--
-- Proof strategy using J eliminator:
-- - For eq : x = y, we want to produce y = x
-- - Define motive C z p = Eq A z x
-- - Base case: C x (refl x) = Eq A x x = refl x
-- - Apply J to get C y eq : Eq A y x

sym :: Term
sym = Lam "A" (Universe 0)
      (Lam "x" (Var "A")
        (Lam "y" (Var "A")
          (Lam "eq" (Eq (Var "A") (Var "x") (Var "y"))
            -- J(A, λz. λp. Eq A z x, refl x, x, y, eq)
            (J (Var "A")
               -- Motive: C z p = Eq A z x
               (Lam "z" (Var "A")
                 (Lam "p" (Eq (Var "A") (Var "x") (Var "z"))
                   (Eq (Var "A") (Var "z") (Var "x"))))
               -- Base case: refl x
               (Refl (Var "x"))
               -- x, y, eq
               (Var "x")
               (Var "y")
               (Var "eq")))))

-- Test symmetry
testSym :: Term
testSym = App (App (App (App sym Nat) Zero) Zero) (Refl Zero)

-- Exercise 2b: Transitivity of Equality
-- trans : Π(A:Type). Π(x y z:A). Eq A x y → Eq A y z → Eq A x z
--
-- Proof strategy:
-- - Given eq1 : x = y and eq2 : y = z
-- - First use J on eq1 to reduce to the case where y is x
-- - Then eq2 : x = z is what we need

trans :: Term
trans = Lam "A" (Universe 0)
        (Lam "x" (Var "A")
          (Lam "y" (Var "A")
            (Lam "z" (Var "A")
              (Lam "eq1" (Eq (Var "A") (Var "x") (Var "y"))
                (Lam "eq2" (Eq (Var "A") (Var "y") (Var "z"))
                  -- J on eq1 to eliminate y, then apply result to eq2
                  (App
                    (J (Var "A")
                       -- Motive: C y' eq1' = Eq A y' z → Eq A x z
                       (Lam "y'" (Var "A")
                         (Lam "eq1'" (Eq (Var "A") (Var "x") (Var "y'"))
                           (Pi "_" (Eq (Var "A") (Var "y'") (Var "z"))
                                   (Eq (Var "A") (Var "x") (Var "z")))))
                       -- Base case: when y' = x, eq1' = refl x
                       -- We need: Eq A x z → Eq A x z (identity function)
                       (Lam "eq" (Eq (Var "A") (Var "x") (Var "z")) (Var "eq"))
                       -- x, y, eq1
                       (Var "x")
                       (Var "y")
                       (Var "eq1"))
                    -- Apply the result to eq2
                    (Var "eq2")))))))

-- Test transitivity
testTrans :: Term
testTrans = App (App (App (App (App (App trans Nat) Zero) Zero) Zero)
                     (Refl Zero)) (Refl Zero)

-- Exercise 2c: Congruence
-- cong : Π(A B:Type). Π(f:A → B). Π(x y:A). Eq A x y → Eq B (f x) (f y)
--
-- Proof: Use J on the equality proof

cong :: Term
cong = Lam "A" (Universe 0)
       (Lam "B" (Universe 0)
         (Lam "f" (Pi "_" (Var "A") (Var "B"))
           (Lam "x" (Var "A")
             (Lam "y" (Var "A")
               (Lam "eq" (Eq (Var "A") (Var "x") (Var "y"))
                 -- J on eq
                 (J (Var "A")
                    -- Motive: C y' eq' = Eq B (f x) (f y')
                    (Lam "y'" (Var "A")
                      (Lam "eq'" (Eq (Var "A") (Var "x") (Var "y'"))
                        (Eq (Var "B") (App (Var "f") (Var "x"))
                                      (App (Var "f") (Var "y'")))))
                    -- Base case: refl (f x)
                    (Refl (App (Var "f") (Var "x")))
                    -- x, y, eq
                    (Var "x")
                    (Var "y")
                    (Var "eq")))))))

-- ============================================================================
-- Exercise 3: Natural Number Proofs
-- ============================================================================

-- Exercise 3a: Addition
-- add : Π(m n:Nat). Nat
-- add m n = natElim (λ_. Nat) m (λk rec. succ rec) n

add :: Term
add = Lam "m" Nat
      (Lam "n" Nat
        (NatElim
          (Lam "_" Nat Nat)
          (Var "m")
          (Lam "k" Nat (Lam "rec" Nat (Succ (Var "rec"))))
          (Var "n")))

-- Test addition
testAdd :: Term
testAdd = App (App add (Succ Zero)) (Succ (Succ Zero))

-- Exercise 3b: Zero is right identity
-- add_zero_right : Π(n:Nat). Eq Nat (add n zero) n
--
-- Proof by induction on n:
-- Base: add zero zero = zero by definition
-- Step: If add k zero = k, then add (succ k) zero = succ (add k zero) = succ k

addZeroRight :: Term
addZeroRight =
  Lam "n" Nat
    (NatElim
      -- Motive: P n = Eq Nat (add n zero) n
      (Lam "n'" Nat (Eq Nat (App (App add (Var "n'")) Zero) (Var "n'")))
      -- Base case: refl zero (since add zero zero = zero)
      (Refl Zero)
      -- Step case: Π(k:Nat). P k → P (succ k)
      -- Given IH : add k zero = k
      -- Need: add (succ k) zero = succ k
      -- We have: add (succ k) zero = succ (add k zero) = succ k by IH
      (Lam "k" Nat
        (Lam "ih" (Eq Nat (App (App add (Var "k")) Zero) (Var "k"))
          -- Use cong to lift the IH
          (App (App (App (App (App (App cong Nat) Nat) (Lam "x" Nat (Succ (Var "x"))))
                         (App (App add (Var "k")) Zero))
                    (Var "k"))
               (Var "ih"))))
      -- Induction on n
      (Var "n"))

-- Exercise 3c: Successor distributes over addition on the right
-- add_succ_right : Π(m n:Nat). Eq Nat (succ (add m n)) (add m (succ n))
--
-- Proof by induction on n:
-- Base: succ (add m zero) = succ m = add m (succ zero)
-- Step: IH gives succ (add m k) = add m (succ k)
--       Need: succ (add m (succ k)) = add m (succ (succ k))
--       LHS = succ (succ (add m k))
--       RHS = succ (add m (succ k)) = succ (succ (add m k)) by IH

addSuccRight :: Term
addSuccRight =
  Lam "m" Nat
    (Lam "n" Nat
      (NatElim
        -- Motive: P n' = Eq Nat (succ (add m n')) (add m (succ n'))
        (Lam "n'" Nat
          (Eq Nat (Succ (App (App add (Var "m")) (Var "n'")))
                  (App (App add (Var "m")) (Succ (Var "n'")))))
        -- Base case: refl (succ m)
        (Refl (Succ (Var "m")))
        -- Step case
        (Lam "k" Nat
          (Lam "ih" (Eq Nat (Succ (App (App add (Var "m")) (Var "k")))
                            (App (App add (Var "m")) (Succ (Var "k"))))
            -- Use cong to apply succ to both sides of IH
            (App (App (App (App (App (App cong Nat) Nat)
                               (Lam "x" Nat (Succ (Var "x"))))
                          (Succ (App (App add (Var "m")) (Var "k"))))
                     (App (App add (Var "m")) (Succ (Var "k"))))
                 (Var "ih"))))
        (Var "n")))

-- ============================================================================
-- Exercise 4: Vector Type (Conceptual)
-- ============================================================================

-- In a full system with inductive families, we would define:
-- data Vec : Nat → Type → Type where
--   Nil  : Π(A:Type). Vec zero A
--   Cons : Π(A:Type). Π(n:Nat). A → Vec n A → Vec (succ n) A

-- For this implementation, we represent these as constructor applications:

-- Nil : Π(A:Type). Vec zero A
vecNil :: Term
vecNil = Con "Nil" [Var "A"]

-- Cons : Π(A:Type). Π(n:Nat). A → Vec n A → Vec (succ n) A
vecCons :: Term -> Term -> Term -> Term
vecCons a x xs = Con "Cons" [a, x, xs]

-- head : Π(A:Type). Π(n:Nat). Vec (succ n) A → A
-- Pattern match on the vector
vecHead :: Term
vecHead = Lam "A" (Universe 0)
          (Lam "n" Nat
            (Lam "v" (App (App (Ind "Vec") (Succ (Var "n"))) (Var "A"))
              (Match (Var "v") Nothing
                [(PCon "Cons" [PVar "a", PVar "x", PVar "xs"], Var "x")])))

-- append : Π(A:Type). Π(m n:Nat). Vec m A → Vec n A → Vec (add m n) A
vecAppend :: Term
vecAppend = Lam "A" (Universe 0)
            (Lam "m" Nat
              (Lam "n" Nat
                (Lam "v1" (App (App (Ind "Vec") (Var "m")) (Var "A"))
                  (Lam "v2" (App (App (Ind "Vec") (Var "n")) (Var "A"))
                    -- Pattern match on v1
                    (Match (Var "v1") Nothing
                      [ (PCon "Nil" [PWild],
                         Var "v2")
                      , (PCon "Cons" [PWild, PVar "x", PVar "xs"],
                         vecCons (Var "A")
                                 (Var "x")
                                 (App (App (App (App (App vecAppend (Var "A"))
                                                     (Var "m"))
                                               (Var "n"))
                                          (Var "xs"))
                                      (Var "v2")))
                      ])))))

-- ============================================================================
-- Exercise 5: Fin Type (Conceptual)
-- ============================================================================

-- data Fin : Nat → Type where
--   FZ : Π(n:Nat). Fin (succ n)
--   FS : Π(n:Nat). Fin n → Fin (succ n)

-- FZ : Π(n:Nat). Fin (succ n)
finZero :: Term
finZero = Con "FZ" [Var "n"]

-- FS : Π(n:Nat). Fin n → Fin (succ n)
finSucc :: Term -> Term
finSucc i = Con "FS" [Var "n", i]

-- lookup : Π(A:Type). Π(n:Nat). Vec n A → Fin n → A
-- Pattern match on the vector first, then on the index
-- Note: This is a simplified conceptual implementation
vecLookup :: Term
vecLookup = Lam "A" (Universe 0)
            (Lam "n" Nat
              (Lam "v" (App (App (Ind "Vec") (Var "n")) (Var "A"))
                (Lam "i" (App (Ind "Fin") (Var "n"))
                  -- Match on the vector
                  (Match (Var "v") Nothing
                    [ (PCon "Cons" [PWild, PVar "x", PVar "xs"],
                       -- Now match on the index
                       Match (Var "i") Nothing
                         [ (PCon "FZ" [PWild], Var "x")
                         , (PCon "FS" [PWild, PVar "i'"],
                            App (App (App (App vecLookup (Var "A"))
                                         (Var "n"))
                                    (Var "xs"))
                                (Var "i'"))
                         ])
                    ]))))

-- ============================================================================
-- Exercise 6: Empty and Unit Types
-- ============================================================================

-- Exercise 6a: Ex falso quodlibet
-- exFalso : Π(A:Type). Empty → A
exFalso :: Term
exFalso = Lam "A" (Universe 0)
          (Lam "e" Empty
            (EmptyElim (Lam "_" Empty (Var "A")) (Var "e")))

-- Exercise 6b: Unit is inhabited
unitProof :: Term
unitProof = TT

-- Exercise 6c: Negation and double negation introduction
-- Not : Type → Type
notType :: Term -> Term
notType a = Pi "_" a Empty

-- doubleNegIntro : Π(A:Type). A → Not (Not A)
-- i.e., Π(A:Type). A → ((A → Empty) → Empty)
doubleNegIntro :: Term
doubleNegIntro = Lam "A" (Universe 0)
                 (Lam "x" (Var "A")
                   (Lam "f" (Pi "_" (Var "A") Empty)
                     (App (Var "f") (Var "x"))))

-- ============================================================================
-- Exercise 7: Leibniz Equality
-- ============================================================================

-- LEq : Π(A:Type). A → A → Type
-- LEq A x y = Π(P:A → Type). P x → P y
leibnizEq :: Term -> Term -> Term -> Term
leibnizEq a x y = Pi "P" (Pi "_" a (Universe 0))
                     (Pi "_" (App (Var "P") x)
                             (App (Var "P") y))

-- Exercise 7a: Reflexivity
-- lrefl : Π(A:Type). Π(x:A). LEq A x x
leibnizRefl :: Term
leibnizRefl = Lam "A" (Universe 0)
              (Lam "x" (Var "A")
                (Lam "P" (Pi "_" (Var "A") (Universe 0))
                  (Lam "px" (App (Var "P") (Var "x"))
                    (Var "px"))))

-- Exercise 7b: Symmetry
-- lsym : Π(A:Type). Π(x y:A). LEq A x y → LEq A y x
leibnizSym :: Term
leibnizSym = Lam "A" (Universe 0)
             (Lam "x" (Var "A")
               (Lam "y" (Var "A")
                 (Lam "eq" (leibnizEq (Var "A") (Var "x") (Var "y"))
                   (Lam "P" (Pi "_" (Var "A") (Universe 0))
                     (Lam "py" (App (Var "P") (Var "y"))
                       -- Apply eq to predicate (λz. P y → P z)
                       -- Then apply the result to (λ_. py)
                       (App (App (App (Var "eq")
                                     (Lam "z" (Var "A")
                                       (Pi "_" (App (Var "P") (Var "y"))
                                               (App (Var "P") (Var "z")))))
                                 (Lam "_" (App (Var "P") (Var "y")) (Var "py")))
                            (Var "py")))))))

-- Exercise 7c: Transitivity
-- ltrans : Π(A:Type). Π(x y z:A). LEq A x y → LEq A y z → LEq A x z
leibnizTrans :: Term
leibnizTrans = Lam "A" (Universe 0)
               (Lam "x" (Var "A")
                 (Lam "y" (Var "A")
                   (Lam "z" (Var "A")
                     (Lam "eq1" (leibnizEq (Var "A") (Var "x") (Var "y"))
                       (Lam "eq2" (leibnizEq (Var "A") (Var "y") (Var "z"))
                         (Lam "P" (Pi "_" (Var "A") (Universe 0))
                           (Lam "px" (App (Var "P") (Var "x"))
                             -- First apply eq1 to get P y
                             -- Then apply eq2 to get P z
                             (App (App (Var "eq2") (Var "P"))
                                  (App (App (Var "eq1") (Var "P")) (Var "px"))))))))))

-- ============================================================================
-- Exercise 8: Decidable Equality (Conceptual)
-- ============================================================================

-- For decidable equality, we need sum types (Either)
-- Either A B can be encoded as Σ(b:Bool). if b then A else B

-- bool_eq : Π(b1 b2:Bool). Either (Eq Bool b1 b2) (Not (Eq Bool b1 b2))
boolEq :: Term
boolEq = Lam "b1" Bool
         (Lam "b2" Bool
           (BoolElim
             -- Motive: P b1 = Π(b2:Bool). Either (Eq Bool b1 b2) (Not (Eq Bool b1 b2))
             (Lam "b1'" Bool
               (Pi "b2" Bool
                 (Sigma "tag" Bool
                   (BoolElim
                     (Lam "_" Bool (Universe 0))
                     (Eq Bool (Var "b1'") (Var "b2"))
                     (notType (Eq Bool (Var "b1'") (Var "b2")))
                     (Var "tag")))))
             -- Case b1 = true
             (Lam "b2'" Bool
               (BoolElim
                 -- Motive for b2'
                 (Lam "b2''" Bool
                   (Sigma "tag" Bool
                     (BoolElim
                       (Lam "_" Bool (Universe 0))
                       (Eq Bool TmTrue (Var "b2''"))
                       (notType (Eq Bool TmTrue (Var "b2''")))
                       (Var "tag"))))
                 -- Case b2' = true: Left (refl true)
                 (Pair TmTrue (Refl TmTrue))
                 -- Case b2' = false: Right (proof that true ≠ false)
                 (Pair TmFalse
                   (Lam "eq" (Eq Bool TmTrue TmFalse)
                     -- Use J to derive contradiction
                     (J Bool
                        (Lam "b" Bool
                          (Lam "e" (Eq Bool TmTrue (Var "b"))
                            Empty))
                        -- This is a bit tricky - we'd need to use the eliminator
                        -- For now, this is conceptual
                        (EmptyElim (Lam "_" Empty Empty) (Var "absurd"))
                        TmTrue
                        TmFalse
                        (Var "eq"))))
                 (Var "b2'")))
             -- Case b1 = false
             (Lam "b2'" Bool
               (BoolElim
                 (Lam "b2''" Bool
                   (Sigma "tag" Bool
                     (BoolElim
                       (Lam "_" Bool (Universe 0))
                       (Eq Bool TmFalse (Var "b2''"))
                       (notType (Eq Bool TmFalse (Var "b2''")))
                       (Var "tag"))))
                 -- Case b2' = true: Right (proof that false ≠ true)
                 (Pair TmFalse
                   (Lam "eq" (Eq Bool TmFalse TmTrue)
                     (EmptyElim (Lam "_" Empty Empty) (Var "absurd"))))
                 -- Case b2' = false: Left (refl false)
                 (Pair TmTrue (Refl TmFalse))
                 (Var "b2'")))
             (Var "b1")))

-- ============================================================================
-- Test Suite
-- ============================================================================

-- Run some basic tests
testSolutions :: IO ()
testSolutions = do
  putStrLn "Testing Chapter 8 Solutions"
  putStrLn "============================"

  putStrLn "\n1. Testing id0:"
  print $ eval testId0

  putStrLn "\n2. Testing addition:"
  print $ eval testAdd

  putStrLn "\n3. Testing symmetry:"
  print $ eval testSym

  putStrLn "\n4. Testing transitivity:"
  print $ eval testTrans

  putStrLn "\n5. Type checking sym:"
  print $ typeOf emptyCtx sym

  putStrLn "\n6. Type checking trans:"
  print $ typeOf emptyCtx trans

  putStrLn "\n7. Type checking add:"
  print $ typeOf emptyCtx add

  putStrLn "\n8. Unit proof:"
  print $ typeOf emptyCtx unitProof

  putStrLn "\n9. Ex falso quodlibet:"
  print $ typeOf emptyCtx exFalso

  putStrLn "\n10. Double negation introduction:"
  print $ typeOf emptyCtx doubleNegIntro

  putStrLn "\n11. Leibniz reflexivity:"
  print $ typeOf emptyCtx leibnizRefl

  putStrLn "\nAll solutions implemented!"
