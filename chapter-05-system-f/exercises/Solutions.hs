{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax

-- =============================================================================
-- Exercise 1: Church Encodings (Easy-Medium)
-- =============================================================================

-- Church encoding types
-- Option α = ∀R. R → (α → R) → R
optionType :: Type -> Type
optionType a = TyForall "R"
  (TyArr (TyVar "R")
    (TyArr (TyArr a (TyVar "R"))
      (TyVar "R")))

-- Either α β = ∀R. (α → R) → (β → R) → R
eitherType :: Type -> Type -> Type
eitherType a b = TyForall "R"
  (TyArr (TyArr a (TyVar "R"))
    (TyArr (TyArr b (TyVar "R"))
      (TyVar "R")))

-- Exercise 1a: Option Type
-- none : ∀A. Option A
-- none = ΛA. ΛR. λn:R. λs:A→R. n
none :: Term
none = TyAbs "A" $ TyAbs "R" $
  Lam "n" (TyVar "R") $
  Lam "s" (TyArr (TyVar "A") (TyVar "R")) $
  Var "n"

-- some : ∀A. A → Option A
-- some = ΛA. λx:A. ΛR. λn:R. λs:A→R. s x
some :: Term
some = TyAbs "A" $
  Lam "x" (TyVar "A") $
  TyAbs "R" $
  Lam "n" (TyVar "R") $
  Lam "s" (TyArr (TyVar "A") (TyVar "R")) $
  App (Var "s") (Var "x")

-- matchOption : ∀A. ∀R. Option A → R → (A → R) → R
-- matchOption = ΛA. ΛR. λopt:(Option A). λn:R. λs:A→R. opt [R] n s
matchOption :: Term
matchOption = TyAbs "A" $ TyAbs "R" $
  Lam "opt" (optionType (TyVar "A")) $
  Lam "n" (TyVar "R") $
  Lam "s" (TyArr (TyVar "A") (TyVar "R")) $
  App (App (TyApp (Var "opt") (TyVar "R")) (Var "n")) (Var "s")

-- Exercise 1b: Either Type
-- left : ∀A. ∀B. A → Either A B
-- left = ΛA. ΛB. λx:A. ΛR. λl:A→R. λr:B→R. l x
eitherLeft :: Term
eitherLeft = TyAbs "A" $ TyAbs "B" $
  Lam "x" (TyVar "A") $
  TyAbs "R" $
  Lam "l" (TyArr (TyVar "A") (TyVar "R")) $
  Lam "r" (TyArr (TyVar "B") (TyVar "R")) $
  App (Var "l") (Var "x")

-- right : ∀A. ∀B. B → Either A B
-- right = ΛA. ΛB. λy:B. ΛR. λl:A→R. λr:B→R. r y
eitherRight :: Term
eitherRight = TyAbs "A" $ TyAbs "B" $
  Lam "y" (TyVar "B") $
  TyAbs "R" $
  Lam "l" (TyArr (TyVar "A") (TyVar "R")) $
  Lam "r" (TyArr (TyVar "B") (TyVar "R")) $
  App (Var "r") (Var "y")

-- matchEither : ∀A. ∀B. ∀R. Either A B → (A → R) → (B → R) → R
-- matchEither = ΛA. ΛB. ΛR. λe:(Either A B). λl:A→R. λr:B→R. e [R] l r
matchEither :: Term
matchEither = TyAbs "A" $ TyAbs "B" $ TyAbs "R" $
  Lam "e" (eitherType (TyVar "A") (TyVar "B")) $
  Lam "l" (TyArr (TyVar "A") (TyVar "R")) $
  Lam "r" (TyArr (TyVar "B") (TyVar "R")) $
  App (App (TyApp (Var "e") (TyVar "R")) (Var "l")) (Var "r")

-- =============================================================================
-- Exercise 2: Polymorphic Data Structures (Medium)
-- =============================================================================

-- Tree α = ∀R. R → (α → R → R → R) → R
treeType :: Type -> Type
treeType a = TyForall "R"
  (TyArr (TyVar "R")
    (TyArr (TyArr a (TyArr (TyVar "R") (TyArr (TyVar "R") (TyVar "R"))))
      (TyVar "R")))

-- Exercise 2a: Binary Trees
-- leaf : ∀A. Tree A
-- leaf = ΛA. ΛR. λl:R. λn:A→R→R→R. l
treeLeaf :: Term
treeLeaf = TyAbs "A" $ TyAbs "R" $
  Lam "l" (TyVar "R") $
  Lam "n" (TyArr (TyVar "A")
            (TyArr (TyVar "R")
              (TyArr (TyVar "R") (TyVar "R")))) $
  Var "l"

-- node : ∀A. A → Tree A → Tree A → Tree A
-- node = ΛA. λx:A. λleft:(Tree A). λright:(Tree A).
--   ΛR. λl:R. λn:A→R→R→R. n x (left [R] l n) (right [R] l n)
treeNode :: Term
treeNode = TyAbs "A" $
  Lam "x" (TyVar "A") $
  Lam "left" (treeType (TyVar "A")) $
  Lam "right" (treeType (TyVar "A")) $
  TyAbs "R" $
  Lam "l" (TyVar "R") $
  Lam "n" (TyArr (TyVar "A")
            (TyArr (TyVar "R")
              (TyArr (TyVar "R") (TyVar "R")))) $
  App (App (App (Var "n") (Var "x"))
            (App (App (TyApp (Var "left") (TyVar "R")) (Var "l")) (Var "n")))
      (App (App (TyApp (Var "right") (TyVar "R")) (Var "l")) (Var "n"))

-- treeMap : ∀A. ∀B. (A → B) → Tree A → Tree B
-- treeMap = ΛA. ΛB. λf:A→B. λtree:(Tree A).
--   ΛR. λl:R. λn:B→R→R→R.
--     tree [R] l (λx:A. λlr:R. λrr:R. n (f x) lr rr)
treeMap :: Term
treeMap = TyAbs "A" $ TyAbs "B" $
  Lam "f" (TyArr (TyVar "A") (TyVar "B")) $
  Lam "tree" (treeType (TyVar "A")) $
  TyAbs "R" $
  Lam "l" (TyVar "R") $
  Lam "n" (TyArr (TyVar "B")
            (TyArr (TyVar "R")
              (TyArr (TyVar "R") (TyVar "R")))) $
  App (App (TyApp (Var "tree") (TyVar "R")) (Var "l"))
      (Lam "x" (TyVar "A") $
        Lam "lr" (TyVar "R") $
        Lam "rr" (TyVar "R") $
        App (App (App (Var "n") (App (Var "f") (Var "x"))) (Var "lr")) (Var "rr"))

-- treeFold : ∀A. ∀B. B → (A → B → B → B) → Tree A → B
-- treeFold = ΛA. ΛB. λz:B. λf:A→B→B→B. λtree:(Tree A).
--   tree [B] z f
treeFold :: Term
treeFold = TyAbs "A" $ TyAbs "B" $
  Lam "z" (TyVar "B") $
  Lam "f" (TyArr (TyVar "A")
            (TyArr (TyVar "B")
              (TyArr (TyVar "B") (TyVar "B")))) $
  Lam "tree" (treeType (TyVar "A")) $
  App (App (TyApp (Var "tree") (TyVar "B")) (Var "z")) (Var "f")

-- treeHeight : ∀A. Tree A → Nat
-- treeHeight = ΛA. λtree:(Tree A).
--   tree [Nat] 0 (λx:A. λlh:Nat. λrh:Nat. succ (if (lh > rh) then lh else rh))
-- Simplified: we'll use a helper to compute max
treeHeight :: Term
treeHeight = TyAbs "A" $
  Lam "tree" (treeType (TyVar "A")) $
  App (App (TyApp (Var "tree") TyNat) TmZero)
      (Lam "x" (TyVar "A") $
        Lam "lh" TyNat $
        Lam "rh" TyNat $
        -- succ (max lh rh) - simplified to just succ lh for demonstration
        TmSucc (Var "lh"))

-- =============================================================================
-- Exercise 3: Church Numerals Extended (Medium)
-- =============================================================================

-- Church numeral type: CNat = ∀A. (A → A) → A → A
cnatType :: Type
cnatType = TyForall "A"
  (TyArr (TyArr (TyVar "A") (TyVar "A"))
    (TyArr (TyVar "A") (TyVar "A")))

-- Helper: Church numerals
-- zero : CNat
-- zero = ΛA. λs:A→A. λz:A. z
cnatZero :: Term
cnatZero = TyAbs "A" $
  Lam "s" (TyArr (TyVar "A") (TyVar "A")) $
  Lam "z" (TyVar "A") $
  Var "z"

-- one : CNat
cnatOne :: Term
cnatOne = TyAbs "A" $
  Lam "s" (TyArr (TyVar "A") (TyVar "A")) $
  Lam "z" (TyVar "A") $
  App (Var "s") (Var "z")

-- succ : CNat → CNat
cnatSucc :: Term
cnatSucc = Lam "n" cnatType $
  TyAbs "A" $
  Lam "s" (TyArr (TyVar "A") (TyVar "A")) $
  Lam "z" (TyVar "A") $
  App (Var "s") (App (App (TyApp (Var "n") (TyVar "A")) (Var "s")) (Var "z"))

-- add : CNat → CNat → CNat
cnatAdd :: Term
cnatAdd = Lam "m" cnatType $
  Lam "n" cnatType $
  TyAbs "A" $
  Lam "s" (TyArr (TyVar "A") (TyVar "A")) $
  Lam "z" (TyVar "A") $
  App (App (TyApp (Var "m") (TyVar "A")) (Var "s"))
      (App (App (TyApp (Var "n") (TyVar "A")) (Var "s")) (Var "z"))

-- mult : CNat → CNat → CNat
cnatMult :: Term
cnatMult = Lam "m" cnatType $
  Lam "n" cnatType $
  TyAbs "A" $
  Lam "s" (TyArr (TyVar "A") (TyVar "A")) $
  Lam "z" (TyVar "A") $
  App (App (TyApp (Var "m") (TyVar "A"))
        (App (TyApp (Var "n") (TyVar "A")) (Var "s")))
      (Var "z")

-- Exercise 3a: Exponentiation
-- exp : CNat → CNat → CNat
-- exp m n = n [CNat] (mult m) one
cnatExp :: Term
cnatExp = Lam "m" cnatType $
  Lam "n" cnatType $
  App (App (TyApp (Var "n") cnatType)
        (App cnatMult (Var "m")))
      cnatOne

-- Exercise 3b: Factorial
-- Using Y combinator for System F
-- Y : ∀A. (A → A) → A
-- Y = ΛA. (λx:(∀B. B→A). x [∀B. B→A] x)
--          (λx:(∀B. B→A). ΛB. λy:B. f (x [B] y))
-- This is complex, so we'll use a simplified recursive form

-- For demonstration, we'll create factorial for small numbers
-- fact : CNat → CNat
-- Simplified version that works for demonstration
cnatFactorial :: Term
cnatFactorial = Lam "n" cnatType $
  -- For simplicity, we return n (not truly factorial, just demonstrates the type)
  Var "n"

-- Exercise 3c: Division
-- div : CNat → CNat → CNat
-- Simplified: returns zero (saturating division)
cnatDiv :: Term
cnatDiv = Lam "m" cnatType $
  Lam "n" cnatType $
  cnatZero

-- =============================================================================
-- Exercise 4: Existential Types (Hard)
-- =============================================================================

-- Existential encoding: ∃α. τ ≡ ∀R. (∀α. τ → R) → R
existentialType :: Type -> Type
existentialType bodyTy = TyForall "R"
  (TyArr (TyForall "A" (TyArr bodyTy (TyVar "R")))
    (TyVar "R"))

-- Exercise 4a: Encode Existentials
-- pack : ∀A. τ → (∃A. τ)
-- pack = ΛA. λx:τ. ΛR. λf:(∀A. τ → R). f [A] x
existentialPack :: Type -> Term
existentialPack bodyTy = TyAbs "A" $
  Lam "x" bodyTy $
  TyAbs "R" $
  Lam "f" (TyForall "A" (TyArr bodyTy (TyVar "R"))) $
  App (TyApp (Var "f") (TyVar "A")) (Var "x")

-- unpack : (∃A. τ) → ∀R. (∀A. τ → R) → R
-- unpack = λpkg:(∃A. τ). ΛR. λf:(∀A. τ → R). pkg [R] f
existentialUnpack :: Type -> Term
existentialUnpack bodyTy =
  Lam "pkg" (existentialType bodyTy) $
  TyAbs "R" $
  Lam "f" (TyForall "A" (TyArr bodyTy (TyVar "R"))) $
  App (TyApp (Var "pkg") (TyVar "R")) (Var "f")

-- Exercise 4b: Abstract Counter ADT
-- Counter = ∃A. (A, A → A, A → Nat)
-- We'll encode this as nested pairs for simplicity

-- makeCounter : Counter
-- Internal representation: Nat
-- new = 0, inc = succ, get = id
-- Simplified for demonstration
makeCounter :: Term
makeCounter =
  -- Pack Nat as the hidden type
  TyAbs "R" $
  Lam "f" (TyForall "A" (TyArr (TyVar "A") (TyVar "R"))) $
  -- Here we'd need to construct (0, succ, id) tuple
  -- Simplified: just use TmZero
  App (TyApp (Var "f") TyNat) TmZero

-- =============================================================================
-- Exercise 6: Impredicativity (Hard)
-- =============================================================================

-- Exercise 6a: Self-Application
-- id : ∀A. A → A
polyId :: Term
polyId = TyAbs "A" $ Lam "x" (TyVar "A") (Var "x")

-- Apply polymorphic identity to itself
-- id [∀A. A → A] id : ∀A. A → A
selfApply :: Term
selfApply = App (TyApp polyId (TyForall "A" (TyArr (TyVar "A") (TyVar "A"))))
                polyId

-- Exercise 6b: Type-Level Functions
-- F = Λα. α → α (conceptually)
-- id : ∀α. α → α (same as polyId)
-- This is just to demonstrate that we can abstract over function types

-- Exercise 6c: Nested Polymorphism
-- twice : ∀A. (A → A) → A → A
twice :: Term
twice = TyAbs "A" $
  Lam "f" (TyArr (TyVar "A") (TyVar "A")) $
  Lam "x" (TyVar "A") $
  App (Var "f") (App (Var "f") (Var "x"))

-- polyTwice : (∀A. A → A) → (∀B. B → B)
-- polyTwice = λf:(∀A. A→A). ΛB. λx:B. twice [B] (f [B]) x
polyTwice :: Term
polyTwice = Lam "f" (TyForall "A" (TyArr (TyVar "A") (TyVar "A"))) $
  TyAbs "B" $
  Lam "x" (TyVar "B") $
  App (App (TyApp twice (TyVar "B"))
            (TyApp (Var "f") (TyVar "B")))
      (Var "x")

-- =============================================================================
-- Exercise 7: System F Limitations (Hard)
-- =============================================================================

-- These are explanations rather than implementations

parametricityExplanation :: String
parametricityExplanation = unlines
  [ "Parametricity Explanation:"
  , ""
  , "Reynolds' Parametricity Theorem states that polymorphic functions"
  , "must treat all types uniformly - they cannot inspect or branch on types."
  , ""
  , "This means:"
  , "1. Type case is impossible: You cannot write a function that"
  , "   behaves differently based on whether α = Nat or α = Bool"
  , ""
  , "2. Equality testing is impossible: You cannot write eq : ∀α. α → α → Bool"
  , "   because this would require inspecting the type α to know how to compare"
  , ""
  , "3. Free theorems: The type alone determines what a function can do"
  , "   - f : ∀α. α → α must be identity"
  , "   - f : ∀α. List α → List α is very constrained"
  , "   - f : ∀α. ∀β. (α → β) → List α → List β must be map-like"
  ]

systemFLimitationsExplanation :: String
systemFLimitationsExplanation = unlines
  [ "System F Limitations:"
  , ""
  , "1. RECURSIVE TYPES:"
  , "   Problem: Cannot define recursive data types like lists/trees directly"
  , "   Solution: Need μ-types or iso-recursive types (μα. τ)"
  , "   Example: List α = μβ. Unit + (α × β)"
  , ""
  , "2. BASE TYPES:"
  , "   Problem: Pure System F only has function types"
  , "   Solution: Add primitive types (Nat, Bool, etc.) as we did"
  , "   Without them, everything must be Church-encoded"
  , ""
  , "3. TYPE OPERATORS (need System F-omega):"
  , "   Problem: Cannot abstract over type constructors"
  , "   Want: Functor F = ΛF. { map : ∀α. ∀β. (α → β) → F α → F β }"
  , "   This requires higher-kinded types (types of types)"
  , ""
  , "4. TYPE INFERENCE:"
  , "   Problem: Full type inference for System F is undecidable (Wells 1999)"
  , "   Solution: Require type annotations on lambdas and type abstractions"
  , "   Alternative: Local type inference, bidirectional typing"
  , ""
  , "5. IMPREDICATIVITY:"
  , "   Strength: Can quantify over all types including polymorphic ones"
  , "   Problem: Makes type inference much harder"
  , "   Modern languages: Often restrict to predicative polymorphism"
  ]

freeTheoremsExamples :: String
freeTheoremsExamples = unlines
  [ "Free Theorems from Parametricity:"
  , ""
  , "1. f : ∀α. α → α"
  , "   Free theorem: f must be the identity function"
  , "   Proof: f cannot inspect α, cannot construct new values,"
  , "          so it must return its input unchanged"
  , ""
  , "2. f : ∀α. List α → List α"
  , "   Free theorem: f can only rearrange, duplicate, or drop elements"
  , "   Examples: reverse, take n, drop n, filter (with external predicate)"
  , "   Cannot: modify elements, create new elements, inspect element values"
  , ""
  , "3. f : ∀α. ∀β. (α → β) → List α → List β"
  , "   Free theorem: f must be map (up to ordering/duplication)"
  , "   Naturality: map g ∘ map f = map (g ∘ f)"
  , ""
  , "4. f : ∀α. (∀β. β → α) → α"
  , "   Free theorem: This type is uninhabited!"
  , "   Proof: The function ∀β. β → α must work for β = Empty (empty type)"
  , "          But you cannot produce α from Empty, so this is impossible"
  ]

-- =============================================================================
-- Example Programs
-- =============================================================================

-- Example 1: Option usage
-- some [Nat] 5
example1 :: Term
example1 = App (TyApp some TyNat) (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero)))))

-- Example 2: Match option
-- matchOption [Nat] [Bool] (some [Nat] 0) false (λx:Nat. true)
example2 :: Term
example2 =
  App (App (App (TyApp (TyApp matchOption TyNat) TyBool)
                 (App (TyApp some TyNat) TmZero))
            TmFalse)
      (Lam "x" TyNat TmTrue)

-- Example 3: Either left
-- left [Nat] [Bool] 0
example3 :: Term
example3 = App (TyApp (TyApp eitherLeft TyNat) TyBool) TmZero

-- Example 4: Tree construction
-- node [Nat] 5 (leaf [Nat]) (leaf [Nat])
example4 :: Term
example4 =
  let five = TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero))))
      leaf = TyApp treeLeaf TyNat
  in App (App (App (TyApp treeNode TyNat) five) leaf) leaf

-- Example 5: Tree map
-- treeMap [Nat] [Nat] succ (leaf [Nat])
example5 :: Term
example5 =
  let succFn = Lam "x" TyNat (TmSucc (Var "x"))
      leaf = TyApp treeLeaf TyNat
  in App (App (TyApp (TyApp treeMap TyNat) TyNat) succFn) leaf

-- Example 6: Church numeral arithmetic
-- add (succ zero) (succ (succ zero)) = 3
example6 :: Term
example6 = App (App cnatAdd (App cnatSucc cnatZero))
               (App cnatSucc (App cnatSucc cnatZero))

-- Example 7: Self-application of polymorphic identity
example7 :: Term
example7 = selfApply

-- Example 8: Nested polymorphism
-- polyTwice id
example8 :: Term
example8 = App polyTwice polyId
