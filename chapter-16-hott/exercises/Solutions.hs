{-# LANGUAGE OverloadedStrings #-}

module Solutions where

import Syntax
import TypeCheck
import qualified Data.Map as Map

-- ============================================================================
-- Exercise 1: Path Basics (Conceptual)
-- ============================================================================

-- 1.1 Understanding Identity Types

-- Question 1: Id Bool true false
-- In classical type theory, this type is empty (uninhabited).
-- We cannot prove true = false without assuming inconsistent axioms.
-- In HoTT, this corresponds to there being no path between true and false.

-- Question 2: Id Nat 0 0
-- This type is inhabited by refl : 0 = 0
-- In HoTT, there may be other paths (higher structure), but we have at least refl.

-- Question 3: Id (Nat → Nat) f g
-- A path between functions represents a homotopy - a continuous deformation
-- from one function to another. With function extensionality, this is
-- equivalent to pointwise equality: ∀x. f x = g x

-- 1.2 Path Induction
-- The J eliminator is valid because of the homotopy interpretation:
-- - To prove something about a path p : a = b, we can assume b = a
-- - Then p = refl by path contraction
-- - So we only need to handle the reflexivity case

-- 1.3 Based Path Induction
-- J and J' are equivalent. J' is "based" at a fixed point a.
-- J' is often more convenient for proofs because it fixes one endpoint.
-- They are interdefinable using path operations.

-- ============================================================================
-- Exercise 2: Path Algebra
-- ============================================================================

-- 2.1 Groupoid Laws
-- Paths form a groupoid where:
-- - refl is the identity
-- - trans is composition
-- - sym is inverse
-- These laws hold definitionally or propositionally depending on the system.

-- Left identity: trans refl p = p
leftIdentity :: Type -> Term -> Term -> Term
leftIdentity ty a b =
  -- Given p : a = b, we want to show trans refl p = p
  -- We use J on p to reduce to the case p = refl
  Lam "p" (TyId ty a b)
    (TmJ (TyId (TyId ty a b)
               (TmTrans (TmRefl ty a) (Var "p"))
               (Var "p"))
         (Lam "x" ty (TmRefl (TyId ty a a) (TmRefl ty (Var "x"))))
         a b (Var "p"))

-- Right identity: trans p refl = p
rightIdentity :: Type -> Term -> Term -> Term
rightIdentity ty a b =
  Lam "p" (TyId ty a b)
    (TmJ (TyId (TyId ty a b)
               (TmTrans (Var "p") (TmRefl ty b))
               (Var "p"))
         (Lam "x" ty (TmRefl (TyId ty a a) (TmRefl ty (Var "x"))))
         a b (Var "p"))

-- Inverse law: trans p (sym p) = refl
inverselaw :: Type -> Term -> Term -> Term
inverselaw ty a b =
  Lam "p" (TyId ty a b)
    (TmJ (TyId (TyId ty a a)
               (TmTrans (Var "p") (TmSym (Var "p")))
               (TmRefl ty a))
         (Lam "x" ty (TmRefl (TyId ty a a) (TmRefl ty (Var "x"))))
         a b (Var "p"))

-- 2.2 Implementing Path Operations with J

-- sym : (p : a = b) → (b = a)
-- Define sym using J with motive C x y p = (y = x)
symViaJ :: Type -> Term -> Term -> Term
symViaJ ty a b =
  Lam "p" (TyId ty a b)
    (TmJ (TyId ty b a)  -- Result type: b = a
         -- Base case: for refl, we return refl
         (Lam "x" ty (TmRefl ty (Var "x")))
         a b (Var "p"))

-- trans : (p : a = b) → (q : b = c) → (a = c)
-- Define trans using J by fixing c and inducting on p
transViaJ :: Type -> Term -> Term -> Term -> Term
transViaJ ty a b c =
  Lam "p" (TyId ty a b)
    (Lam "q" (TyId ty b c)
      (TmJ (TyId ty a c)  -- Result type: a = c
           -- Base case: when p = refl, we have a = b = a, so we return q
           (Lam "x" ty (Var "q"))
           a b (Var "p")))

-- 2.3 Action on Paths
-- ap : (f : A → B) → (p : a = b) → (f a = f b)
actionOnPaths :: Type -> Type -> Term -> Term -> Term -> Term
actionOnPaths tyA tyB f a b =
  Lam "p" (TyId tyA a b)
    (TmAp f (Var "p"))

-- Property 1: ap id p = p
apId :: Type -> Term -> Term -> Term
apId ty a b =
  Lam "p" (TyId ty a b)
    (TmJ (TyId (TyId ty a b)
               (TmAp (Lam "x" ty (Var "x")) (Var "p"))
               (Var "p"))
         (Lam "x" ty (TmRefl (TyId ty a a) (TmRefl ty (Var "x"))))
         a b (Var "p"))

-- Property 2: ap f refl = refl
apRefl :: Type -> Type -> Term -> Term -> Term
apRefl tyA tyB f a =
  TmRefl (TyId tyB (App f a) (App f a))
         (TmAp f (TmRefl tyA a))

-- ============================================================================
-- Exercise 3: Transport and Path Lifting
-- ============================================================================

-- 3.1 Understanding Transport
-- transport : (P : A → Type) → (p : a = b) → P a → P b

-- If P x = (x = x), then transport P p refl transports a loop at a
-- to a loop at b. This creates conjugation: p⁻¹ ∘ refl ∘ p = refl

transportExample :: Type -> Term -> Term -> Term
transportExample ty a b =
  Lam "p" (TyId ty a b)
    (TmTransport (TyId ty b b)
                 (Var "p")
                 (TmRefl ty a))

-- 3.2 Path Lifting
-- lift : (P : A → Type) → (p : a = b) → (u : P a) → Σ(v : P b). transport P p u = v
-- This exists with v = transport P p u
-- The equality is refl by definition of transport

-- 3.3 Dependent Paths
-- If P is constant (P x = B for all x), then:
-- PathOver P p u v ≡ transport P p u = v ≡ u = v
-- because transport along a constant family is the identity

-- ============================================================================
-- Exercise 4: Higher Paths
-- ============================================================================

-- 4.1 Paths Between Paths
-- A 2-path (element of Id (Id A a b) p q) represents a homotopy between
-- paths p and q. Geometrically, it's a continuous deformation of path p
-- into path q, like a filled square.

-- 4.2 Loop Spaces
-- Ω(A, a) = Id A a a is the space of loops at a
-- Ω²(A, a) = Id (Id A a a) refl refl is the space of 2-loops

-- Example: refl is always a loop
loopRefl :: Type -> Term -> Term
loopRefl ty a = TmRefl ty a

-- A 2-loop is a path between refl and refl
twoLoopRefl :: Type -> Term -> Term
twoLoopRefl ty a = TmRefl (TyId ty a a) (TmRefl ty a)

-- 4.3 The Eckmann-Hilton Argument
-- For 2-loops α, β : refl = refl, we have:
-- - Vertical composition: α ∘ᵥ β
-- - Horizontal composition: α ∘ₕ β
-- These are equal: α ∘ᵥ β = α ∘ₕ β
-- Moreover, both are commutative!
-- This shows Ω²(A,a) is abelian even if Ω(A,a) is not.

-- ============================================================================
-- Exercise 5: Function Extensionality
-- ============================================================================

-- 5.1 The Problem
-- funext : (f g : A → B) → ((x : A) → f x = g x) → f = g
-- This cannot be proved using only J because J only allows us to
-- eliminate paths in the domain, not construct paths between functions.

-- 5.2 Weak Function Extensionality
-- If we have funext, then weak funext follows:
-- Given pointwise equality h : (x : A) → f x = g x
-- We get p : f = g from funext
-- Then f = g is contractible with center p

-- 5.3 Happly
-- happly : (p : f = g) → (x : A) → f x = g x
-- This is definable as: happly p x = ap (λf. f x) p

happly :: Type -> Type -> Term -> Term -> Term -> Term -> Term
happly tyA tyB f g x p =
  TmAp (Lam "fn" (TyFun tyA tyB) (App (Var "fn") x)) p

-- Example use of happly
happlyExample :: Term
happlyExample =
  Lam "f" (TyFun TyNat TyBool)
    (Lam "g" (TyFun TyNat TyBool)
      (Lam "p" (TyId (TyFun TyNat TyBool)
                     (Var "f") (Var "g"))
        (Lam "x" TyNat
          (happly TyNat TyBool
                  (Var "f") (Var "g")
                  (Var "x") (Var "p")))))

-- ============================================================================
-- Exercise 6: The Univalence Axiom
-- ============================================================================

-- 6.1 Type Equivalence
-- A ≃ B = Σ(f : A → B). isEquiv f
-- where isEquiv f means f has a quasi-inverse

-- Reflexivity: A ≃ A via the identity function
idEquiv :: Type -> Term
idEquiv ty =
  TmPair (Lam "x" ty (Var "x"))  -- The identity function
         (TmPair (Lam "x" ty (Var "x"))  -- Its inverse (also id)
           (TmPair TmUnit TmUnit))  -- Proofs that it's an equivalence

-- 6.2 idtoeqv
-- idtoeqv : (p : A = B) → (A ≃ B)
-- This uses transport: given p : A = B, we transport the identity function
-- transport (λX. A → X) p id : A → B

-- Transport gives an equivalence because:
-- - It has an inverse (transport along p⁻¹)
-- - These compose to identity (by path algebra)

-- 6.3 The Univalence Axiom
-- ua : (A ≃ B) ≃ (A = B)
-- This states that equivalent types are equal.
-- Not provable in MLTT because we cannot construct paths between types
-- from equivalences without an axiom.

-- Consequences:
-- - Function extensionality follows from univalence
-- - Allows computational reasoning about type equivalences
-- - Makes the universe of types into a higher groupoid

-- 6.4 Boolean Negation
-- not : Bool → Bool is an equivalence (involution)
-- By univalence: notPath : Bool = Bool
-- transport (λX. X) notPath true = not true = false

boolNot :: Term
boolNot = Lam "b" TyBool
          (TmIf (Var "b") TmFalse TmTrue)

-- ============================================================================
-- Exercise 7: Higher Inductive Types
-- ============================================================================

-- 7.1 The Circle
-- S¹ is defined with:
-- - A point constructor: base : S¹
-- - A path constructor: loop : base = base
-- This is different from regular inductive types because we have
-- a constructor for paths, not just points.

-- 7.2 Circle Induction
-- The induction principle for S¹ requires:
-- - A value at base: b : P base
-- - A path over loop: l : PathOver P loop b b
-- This is different from Bool which only needs two values.
-- The path constructor requires a dependent path.

-- 7.3 The Fundamental Group
-- π₁(S¹) ≃ ℤ means:
-- - Loops at base correspond to integers (winding numbers)
-- - Concatenating loops corresponds to adding integers
-- - The inverse path corresponds to negation
-- Intuitively: a loop winds around the circle some number of times

-- ============================================================================
-- Practical Examples
-- ============================================================================

-- Example 1: Symmetry of equality for Nats
symNat :: Term -> Term -> Term
symNat a b =
  Lam "p" (TyId TyNat a b)
    (TmSym (Var "p"))

-- Example 2: Transitivity for Nats
transNat :: Term -> Term -> Term -> Term
transNat a b c =
  Lam "p" (TyId TyNat a b)
    (Lam "q" (TyId TyNat b c)
      (TmTrans (Var "p") (Var "q")))

-- Example 3: Congruence - successor preserves equality
succCong :: Term -> Term -> Term
succCong a b =
  Lam "p" (TyId TyNat a b)
    (TmAp (Lam "x" TyNat (TmSucc (Var "x")))
          (Var "p"))

-- Example 4: Using J to prove a property
-- Prove that for all p : a = b, we have p = p (trivial but demonstrates J)
pathEqItself :: Type -> Term -> Term -> Term
pathEqItself ty a b =
  Lam "p" (TyId ty a b)
    (TmJ (TyId (TyId ty a b) (Var "p") (Var "p"))
         (Lam "x" ty (TmRefl (TyId ty a a) (TmRefl ty (Var "x"))))
         a b (Var "p"))

-- Example 5: Transport along a path in Nat
transportNat :: Term -> Term -> Term
transportNat a b =
  Lam "p" (TyId TyNat a b)
    (Lam "x" TyNat
      (TmTransport TyNat (Var "p") (Var "x")))

-- ============================================================================
-- Challenge Problem Solutions (Conceptual)
-- ============================================================================

-- Challenge 1: Encode-Decode
-- To show Nat = Nat has exactly two elements (id and ???):
-- We use the encode-decode method. For Nat, any equivalence is determined
-- by where it sends 0. If it sends 0 to 0, it must be the identity.
-- If it sends 0 to some other value... actually, for Nat there might be
-- many equivalences! This challenge is more subtle than it appears.

-- Challenge 2: Hedberg's Theorem
-- If A has decidable equality, then A is a set.
-- Proof sketch:
-- 1. Decidable equality gives a choice function for paths
-- 2. This allows us to show all paths between equal elements are equal
-- 3. Therefore A satisfies the set axiom (UIP - uniqueness of identity proofs)

-- Challenge 3: The Suspension
-- Σ Bool has north, south, and two meridians (one for true, one for false)
-- S¹ has base and loop
-- The equivalence maps:
-- - north ↦ base
-- - south ↦ base
-- - merid true ↦ loop
-- - merid false ↦ refl
-- This shows that "suspending" a discrete space creates a circle

-- ============================================================================
-- Test Suite
-- ============================================================================

-- Test symmetry
testSym :: Either TypeError Type
testSym = typeCheck (symNat TmZero (TmSucc TmZero))

-- Test transitivity
testTrans :: Either TypeError Type
testTrans = typeCheck (transNat TmZero (TmSucc TmZero) (TmSucc (TmSucc TmZero)))

-- Test congruence
testCong :: Either TypeError Type
testCong = typeCheck (succCong TmZero (TmSucc TmZero))

-- Test happly
testHapply :: Either TypeError Type
testHapply = typeCheck happlyExample

-- Test J eliminator
testJ :: Either TypeError Type
testJ = typeCheck (pathEqItself TyNat TmZero TmZero)

-- Run all tests
runTests :: IO ()
runTests = do
  putStrLn "Chapter 16: Homotopy Type Theory - Solutions"
  putStrLn "=============================================="

  putStrLn "\nTest 1: Symmetry of equality"
  print testSym

  putStrLn "\nTest 2: Transitivity of equality"
  print testTrans

  putStrLn "\nTest 3: Congruence (ap)"
  print testCong

  putStrLn "\nTest 4: Happly (path elimination for functions)"
  print testHapply

  putStrLn "\nTest 5: J eliminator"
  print testJ

  putStrLn "\nAll tests complete!"

-- ============================================================================
-- Additional Helper Functions
-- ============================================================================

-- Create a reflexivity proof
mkRefl :: Type -> Term -> Term
mkRefl ty t = TmRefl ty t

-- Create a symmetry proof
mkSym :: Term -> Term
mkSym = TmSym

-- Create a transitivity proof
mkTrans :: Term -> Term -> Term
mkTrans = TmTrans

-- Create an ap proof
mkAp :: Term -> Term -> Term
mkAp = TmAp

-- Example: Prove 0 = 0
proof_0_eq_0 :: Term
proof_0_eq_0 = TmRefl TyNat TmZero

-- Example: Given p : 1 = 2, prove 2 = 1
proof_sym_example :: Term
proof_sym_example =
  Lam "p" (TyId TyNat (TmSucc TmZero) (TmSucc (TmSucc TmZero)))
    (TmSym (Var "p"))

-- Example: Given p : 0 = 1 and q : 1 = 2, prove 0 = 2
proof_trans_example :: Term
proof_trans_example =
  Lam "p" (TyId TyNat TmZero (TmSucc TmZero))
    (Lam "q" (TyId TyNat (TmSucc TmZero) (TmSucc (TmSucc TmZero)))
      (TmTrans (Var "p") (Var "q")))

-- Example: Given p : 0 = 1, prove (succ 0) = (succ 1)
proof_ap_example :: Term
proof_ap_example =
  Lam "p" (TyId TyNat TmZero (TmSucc TmZero))
    (TmAp (Lam "x" TyNat (TmSucc (Var "x"))) (Var "p"))
