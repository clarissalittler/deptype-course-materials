{-# LANGUAGE OverloadedStrings #-}

module Solutions where

import Syntax

-- ============================================================================
-- Exercise 1: Basic Type Operators
-- ============================================================================

-- | 1a. Identity type operator: λA::*. A
-- Kind: * → *
idOp :: Type
idOp = TyLam "A" KStar (TyVar "A")

-- | 1b. Const type operator: λA::*. λB::*. A
-- Kind: * → * → *
-- Takes two types and returns the first
constOp :: Type
constOp = TyLam "A" KStar (TyLam "B" KStar (TyVar "A"))

-- | 1c. Compose type operators: λF::* → *. λG::* → *. λA::*. F (G A)
-- Kind: (* → *) → (* → *) → * → *
-- Composes two type constructors
composeOp :: Type
composeOp = TyLam "F" (KArr KStar KStar)
              (TyLam "G" (KArr KStar KStar)
                (TyLam "A" KStar
                  (TyApp (TyVar "F") (TyApp (TyVar "G") (TyVar "A")))))

-- ============================================================================
-- Exercise 2: List Type Constructor
-- ============================================================================

-- | 2a. List type constructor
-- In System F-omega, we encode List as a type operator:
-- List = λA::*. ∀R::*. R → (A → R → R) → R
--
-- This is the Church encoding of lists at the type level.
-- A list of A's is a fold: given a nil value and a cons function, produce R.
listType :: Type
listType = TyLam "A" KStar
             (TyForall "R" KStar
               (TyArr (TyVar "R")
                 (TyArr (TyArr (TyVar "A") (TyArr (TyVar "R") (TyVar "R")))
                   (TyVar "R"))))

-- | 2b. List Bool is just (List Bool)
-- This is handled by type application: TyApp listType TyBool

-- | 2c. Nil constructor: ΛA::*. ΛR::*. λnil:R. λcons:A → R → R. nil
-- Type: ∀A::*. List A
nil :: Term
nil = TyAbs "A" KStar
        (TyAbs "R" KStar
          (Lam "nil" (TyVar "R")
            (Lam "cons" (TyArr (TyVar "A") (TyArr (TyVar "R") (TyVar "R")))
              (Var "nil"))))

-- | 2d. Cons constructor (simplified for type-checking)
-- Type: ∀A::*. A → List A → List A
cons :: Term
cons = TyAbs "A" KStar
         (Lam "head" (TyVar "A")
           (Lam "tail" (TyApp listType (TyVar "A"))
             (TyAbs "R" KStar
               (Lam "nil" (TyVar "R")
                 (Lam "consFunc" (TyArr (TyVar "A") (TyArr (TyVar "R") (TyVar "R")))
                   (App (App (Var "consFunc") (Var "head"))
                     (App (App (TyAppTerm (Var "tail") (TyVar "R")) (Var "nil")) (Var "consFunc"))))))))

-- ============================================================================
-- Exercise 3: Maybe Type Constructor
-- ============================================================================

-- | 3a. Maybe type constructor: λA::*. ∀R::*. R → (A → R) → R
-- Kind: * → *
maybeType :: Type
maybeType = TyLam "A" KStar
              (TyForall "R" KStar
                (TyArr (TyVar "R")
                  (TyArr (TyArr (TyVar "A") (TyVar "R"))
                    (TyVar "R"))))

-- | 3b. Nothing: ΛA::*. ΛR::*. λnothing:R. λjust:A → R. nothing
-- Type: ∀A::*. Maybe A
nothing :: Term
nothing = TyAbs "A" KStar
            (TyAbs "R" KStar
              (Lam "nothing" (TyVar "R")
                (Lam "just" (TyArr (TyVar "A") (TyVar "R"))
                  (Var "nothing"))))

-- | 3c. Just: ΛA::*. λvalue:A. ΛR::*. λnothing:R. λjust:A → R. just value
-- Type: ∀A::*. A → Maybe A
just :: Term
just = TyAbs "A" KStar
         (Lam "value" (TyVar "A")
           (TyAbs "R" KStar
             (Lam "nothing" (TyVar "R")
               (Lam "just" (TyArr (TyVar "A") (TyVar "R"))
                 (App (Var "just") (Var "value"))))))

-- ============================================================================
-- Exercise 4: Either Type Constructor
-- ============================================================================

-- | 4a. Either type constructor: λA::*. λB::*. ∀R::*. (A → R) → (B → R) → R
-- Kind: * → * → *
eitherType :: Type
eitherType = TyLam "A" KStar
               (TyLam "B" KStar
                 (TyForall "R" KStar
                   (TyArr (TyArr (TyVar "A") (TyVar "R"))
                     (TyArr (TyArr (TyVar "B") (TyVar "R"))
                       (TyVar "R")))))

-- | 4b. Either Bool Nat is handled by type application

-- | 4c. Left injection: ΛA::*. ΛB::*. λvalue:A. ΛR::*. λleft:A → R. λright:B → R. left value
-- Type: ∀A::*. ∀B::*. A → Either A B
leftInj :: Term
leftInj = TyAbs "A" KStar
            (TyAbs "B" KStar
              (Lam "value" (TyVar "A")
                (TyAbs "R" KStar
                  (Lam "left" (TyArr (TyVar "A") (TyVar "R"))
                    (Lam "right" (TyArr (TyVar "B") (TyVar "R"))
                      (App (Var "left") (Var "value")))))))

-- | 4d. Right injection: ΛA::*. ΛB::*. λvalue:B. ΛR::*. λleft:A → R. λright:B → R. right value
-- Type: ∀A::*. ∀B::*. B → Either A B
rightInj :: Term
rightInj = TyAbs "A" KStar
             (TyAbs "B" KStar
               (Lam "value" (TyVar "B")
                 (TyAbs "R" KStar
                   (Lam "left" (TyArr (TyVar "A") (TyVar "R"))
                     (Lam "right" (TyArr (TyVar "B") (TyVar "R"))
                       (App (Var "right") (Var "value")))))))

-- ============================================================================
-- Exercise 6: Type-Level Church Encodings
-- ============================================================================

-- | 6a. Type-level Church boolean encoding
-- A type-level boolean is a type that chooses between two types
-- CBool = ∀A::*. A → A → A (same as System F)
tyChurchBool :: Type
tyChurchBool = TyForall "A" KStar
                 (TyArr (TyVar "A") (TyArr (TyVar "A") (TyVar "A")))

-- | 6b. Type-level if: λC::*. λT::*. λF::*. C T F
-- This assumes C is a Church boolean at type level
-- Kind: * → * → * → *
tyIf :: Type
tyIf = TyLam "C" KStar
         (TyLam "T" KStar
           (TyLam "F" KStar
             (TyApp (TyApp (TyVar "C") (TyVar "T")) (TyVar "F"))))

-- ============================================================================
-- Exercise 7: Product and Sum at Type Level
-- ============================================================================

-- | 7a. Product type operator: λA::*. λB::*. ∀R::*. (A → B → R) → R
-- Kind: * → * → *
tyProduct :: Type
tyProduct = TyLam "A" KStar
              (TyLam "B" KStar
                (TyForall "R" KStar
                  (TyArr (TyArr (TyVar "A") (TyArr (TyVar "B") (TyVar "R")))
                    (TyVar "R"))))

-- | 7b. Sum type operator (same as Either)
-- Kind: * → * → *
tySum :: Type
tySum = eitherType  -- Either is the same as sum type

-- ============================================================================
-- Example: Using the type operators
-- ============================================================================

-- | Example: List of Booleans
listBool :: Type
listBool = TyApp listType TyBool

-- | Example: Maybe Nat
maybeNat :: Type
maybeNat = TyApp maybeType TyNat

-- | Example: Either Bool Nat
eitherBoolNat :: Type
eitherBoolNat = TyApp (TyApp eitherType TyBool) TyNat

-- | Example: Composing Maybe and List gives λA::*. Maybe (List A)
maybeList :: Type
maybeList = composeOp `TyApp` maybeType `TyApp` listType
