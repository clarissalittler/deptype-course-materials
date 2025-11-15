module Solutions where

import Syntax

-- ============================================================================
-- Exercise 1: Basic Dependent Functions
-- ============================================================================

-- | 1a. Polymorphic Identity
-- id : Π(A:Type). A → A
polyId :: Term
polyId = Lam "A" Type (Lam "x" (Var "A") (Var "x"))

-- Test: (id Nat 0) should evaluate to 0
testPolyId :: Term
testPolyId = App (App polyId Nat) Zero

-- | 1b. Polymorphic Const
-- const : Π(A:Type). Π(B:Type). A → B → A
polyConst :: Term
polyConst = Lam "A" Type
              (Lam "B" Type
                (Lam "x" (Var "A")
                  (Lam "y" (Var "B") (Var "x"))))

-- Test: const Nat Bool 0 true → 0
testPolyConst :: Term
testPolyConst = App (App (App (App polyConst Nat) Bool) Zero) TmTrue

-- | 1c. Polymorphic Compose
-- compose : Π(A:Type). Π(B:Type). Π(C:Type). (B → C) → (A → B) → A → C
polyCompose :: Term
polyCompose = Lam "A" Type
                (Lam "B" Type
                  (Lam "C" Type
                    (Lam "g" (Pi "x" (Var "B") (Var "C"))
                      (Lam "f" (Pi "y" (Var "A") (Var "B"))
                        (Lam "x" (Var "A")
                          (App (Var "g") (App (Var "f") (Var "x"))))))))

-- ============================================================================
-- Exercise 2: Dependent Pairs (Sigma Types)
-- ============================================================================

-- | 2a. Dependent Pair Creation
-- TypeAndValue : Type
-- TypeAndValue = Σ(A:Type). A
typeAndValue :: Term
typeAndValue = Sigma "A" Type (Var "A")

-- Example: (Nat, 0) : TypeAndValue
exampleTypeAndValue :: Term
exampleTypeAndValue = Pair Nat Zero

-- | 2c. Sigma Swap
-- swap : Σ(x:Nat). Nat → Σ(y:Nat). Nat
-- swap p = (snd p, fst p)
sigmaSwap :: Term
sigmaSwap = Lam "p" (Sigma "x" Nat Nat)
              (Pair (Snd (Var "p")) (Fst (Var "p")))

-- ============================================================================
-- Exercise 4: Church Encodings with Dependent Types
-- ============================================================================

-- | 4a. Polymorphic Church Booleans
-- CBool : Type
-- CBool = Π(A:Type). A → A → A
cBoolType :: Term
cBoolType = Pi "A" Type (Pi "t" (Var "A") (Pi "f" (Var "A") (Var "A")))

-- ctrue : CBool
-- ctrue = λ(A:Type). λ(t:A). λ(f:A). t
cTrue :: Term
cTrue = Lam "A" Type
          (Lam "t" (Var "A")
            (Lam "f" (Var "A") (Var "t")))

-- cfalse : CBool
-- cfalse = λ(A:Type). λ(t:A). λ(f:A). f
cFalse :: Term
cFalse = Lam "A" Type
           (Lam "t" (Var "A")
             (Lam "f" (Var "A") (Var "f")))

-- | 4b. Church Boolean Operations
-- cand : CBool → CBool → CBool
cAnd :: Term
cAnd = Lam "p" cBoolType
         (Lam "q" cBoolType
           (Lam "A" Type
             (Lam "t" (Var "A")
               (Lam "f" (Var "A")
                 (App (App (App (Var "p") (Var "A"))
                           (App (App (App (Var "q") (Var "A")) (Var "t")) (Var "f")))
                      (Var "f"))))))

-- cor : CBool → CBool → CBool
cOr :: Term
cOr = Lam "p" cBoolType
        (Lam "q" cBoolType
          (Lam "A" Type
            (Lam "t" (Var "A")
              (Lam "f" (Var "A")
                (App (App (App (Var "p") (Var "A")) (Var "t"))
                     (App (App (App (Var "q") (Var "A")) (Var "t")) (Var "f")))))))

-- cnot : CBool → CBool
cNot :: Term
cNot = Lam "p" cBoolType
         (Lam "A" Type
           (Lam "t" (Var "A")
             (Lam "f" (Var "A")
               (App (App (App (Var "p") (Var "A")) (Var "f")) (Var "t")))))

-- | 4c. Polymorphic Church Numerals
-- CNat : Type
-- CNat = Π(A:Type). (A → A) → A → A
cNatType :: Term
cNatType = Pi "A" Type
             (Pi "f" (Pi "x" (Var "A") (Var "A"))
               (Pi "z" (Var "A") (Var "A")))

-- czero : CNat
cZero :: Term
cZero = Lam "A" Type
          (Lam "f" (Pi "x" (Var "A") (Var "A"))
            (Lam "z" (Var "A") (Var "z")))

-- csucc : CNat → CNat
cSucc :: Term
cSucc = Lam "n" cNatType
          (Lam "A" Type
            (Lam "f" (Pi "x" (Var "A") (Var "A"))
              (Lam "z" (Var "A")
                (App (Var "f")
                     (App (App (App (Var "n") (Var "A")) (Var "f")) (Var "z"))))))

-- ============================================================================
-- Exercise 5: Existential Types via Sigma
-- ============================================================================

-- | 5a. Abstract Data Type
-- AbstractNat : Type
-- AbstractNat = Σ(Rep:Type). (Rep × (Rep → Nat))
abstractNatType :: Term
abstractNatType = Sigma "Rep" Type
                    (Sigma "value" (Var "Rep")
                      (Pi "x" (Var "Rep") Nat))

-- Example using Bool as representation
-- False represents 0, True represents 1
exampleAbstractNat :: Term
exampleAbstractNat =
  Pair Bool
    (Pair TmFalse
      (Lam "b" Bool (If (Var "b") (Succ Zero) Zero)))

-- ============================================================================
-- Exercise 6: Proof-Relevant Programming
-- ============================================================================

-- | 6a. Non-Empty Type
-- Inhabited : Type → Type
-- Inhabited A = A
inhabitedType :: Term -> Term
inhabitedType a = a

-- proofNatInhabited : Inhabited Nat
proofNatInhabited :: Term
proofNatInhabited = Zero

-- proofBoolInhabited : Inhabited Bool
proofBoolInhabited :: Term
proofBoolInhabited = TmTrue

-- | 6b. Function Type as Implication
-- natToNat : Nat → Nat (proof that Nat implies Nat)
natToNat :: Term
natToNat = Lam "n" Nat (Var "n")

-- | 6c. Pair Type as Conjunction
-- natAndBool : Σ(x:Nat). Bool (proof that we have both Nat and Bool)
natAndBool :: Term
natAndBool = Pair Zero TmTrue

-- ============================================================================
-- Exercise 7: Dependent Type Utilities
-- ============================================================================

-- | 7a. Apply Function
-- apply : Π(A:Type). Π(B:Type). (A → B) → A → B
applyFun :: Term
applyFun = Lam "A" Type
             (Lam "B" Type
               (Lam "f" (Pi "x" (Var "A") (Var "B"))
                 (Lam "x" (Var "A")
                   (App (Var "f") (Var "x")))))

-- | 7b. Flip Arguments
-- flip : Π(A:Type). Π(B:Type). Π(C:Type). (A → B → C) → B → A → C
flipFun :: Term
flipFun = Lam "A" Type
            (Lam "B" Type
              (Lam "C" Type
                (Lam "f" (Pi "x" (Var "A") (Pi "y" (Var "B") (Var "C")))
                  (Lam "y" (Var "B")
                    (Lam "x" (Var "A")
                      (App (App (Var "f") (Var "x")) (Var "y")))))))

-- | 7c. Curry
-- curry : Π(A:Type). Π(B:Type). Π(C:Type).
--         (Σ(x:A). B → C) → A → B → C
curryFun :: Term
curryFun = Lam "A" Type
             (Lam "B" Type
               (Lam "C" Type
                 (Lam "f" (Pi "p" (Sigma "x" (Var "A") (Var "B")) (Var "C"))
                   (Lam "x" (Var "A")
                     (Lam "y" (Var "B")
                       (App (Var "f") (Pair (Var "x") (Var "y"))))))))

-- | 7c. Uncurry
-- uncurry : Π(A:Type). Π(B:Type). Π(C:Type).
--           (A → B → C) → Σ(x:A). B → C
uncurryFun :: Term
uncurryFun = Lam "A" Type
               (Lam "B" Type
                 (Lam "C" Type
                   (Lam "f" (Pi "x" (Var "A") (Pi "y" (Var "B") (Var "C")))
                     (Lam "p" (Sigma "x" (Var "A") (Var "B"))
                       (App (App (Var "f") (Fst (Var "p"))) (Snd (Var "p")))))))

-- ============================================================================
-- Additional Examples
-- ============================================================================

-- | K combinator with dependent types
kCombinator :: Term
kCombinator = Lam "A" Type
                (Lam "B" Type
                  (Lam "x" (Var "A")
                    (Lam "y" (Var "B") (Var "x"))))

-- | S combinator with dependent types
sCombinator :: Term
sCombinator = Lam "A" Type
                (Lam "B" Type
                  (Lam "C" Type
                    (Lam "f" (Pi "x" (Var "A") (Pi "y" (Var "B") (Var "C")))
                      (Lam "g" (Pi "x" (Var "A") (Var "B"))
                        (Lam "x" (Var "A")
                          (App (App (Var "f") (Var "x"))
                               (App (Var "g") (Var "x"))))))))

-- | Dependent pair of a type and a function on that type
typeFunctionPair :: Term
typeFunctionPair = Sigma "A" Type (Pi "x" (Var "A") (Var "A"))

-- Example: (Nat, succ)
exampleTypeFunctionPair :: Term
exampleTypeFunctionPair = Pair Nat (Lam "n" Nat (Succ (Var "n")))

-- | Proof that Bool implies Bool
boolImpliesBool :: Term
boolImpliesBool = Lam "b" Bool (Var "b")

-- | Proof that Nat implies Nat
natImpliesNat :: Term
natImpliesNat = Lam "n" Nat (Var "n")

-- | Transitivity of implication
-- If A → B and B → C, then A → C
transitivity :: Term
transitivity = Lam "A" Type
                 (Lam "B" Type
                   (Lam "C" Type
                     (Lam "f" (Pi "x" (Var "A") (Var "B"))
                       (Lam "g" (Pi "y" (Var "B") (Var "C"))
                         (Lam "x" (Var "A")
                           (App (Var "g") (App (Var "f") (Var "x"))))))))
