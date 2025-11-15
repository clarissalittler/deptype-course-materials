{-# LANGUAGE LambdaCase #-}

module Hints where

import Syntax

{-|
CHAPTER 5 EXERCISE HINTS

This file provides scaffolding and hints for Chapter 5 exercises.
Try implementing solutions yourself before looking at Solutions.hs!

Chapter 5 introduces System F (polymorphic lambda calculus) with:
- Type abstraction: ΛA. t
- Type application: t [τ]
- Impredicative polymorphism
- Explicit type arguments

KEY DIFFERENCES FROM HINDLEY-MILNER:
- Type inference is UNDECIDABLE (must provide annotations)
- Type application is EXPLICIT (must write [τ])
- More expressive (rank-n types, impredicativity)
- Can encode more data structures

MAIN LEARNING GOALS:
1. Church encodings at the type level
2. Explicit type abstraction/application
3. Parametricity and free theorems
4. Existential types via encoding
5. Understanding impredicativity
-}

-- =============================================================================
-- Helper Functions (Provided)
-- =============================================================================

-- Church numeral type: CNat = ∀A. (A → A) → A → A
cnatType :: Type
cnatType = TyForall "A"
  (TyArr (TyArr (TyVar "A") (TyVar "A"))
    (TyArr (TyVar "A") (TyVar "A")))

-- =============================================================================
-- Exercise 1: Church Encodings (Easy-Medium)
-- =============================================================================

{- Exercise 1: Church Encodings for ADTs

In System F, we can encode algebraic data types as functions!
This is called "Church encoding" or "Böhm-Berarducci encoding".

KEY IDEA: A data type is represented by its eliminator.
"To have something is to know what to do with it."

GENERAL PATTERN:
  data T α = C₁ τ₁ | C₂ τ₂ | ... | Cₙ τₙ

Encodes to:
  T α = ∀R. (τ₁ → R) → (τ₂ → R) → ... → (τₙ → R) → R

Each constructor becomes a continuation that gets called.
-}

{- Exercise 1a: Option Type

DEFINITION:
  data Option α = None | Some α

ENCODING:
  Option α = ∀R. R → (α → R) → R

  Reading: "An option is a value that, given:
    - what to do in the None case (R)
    - what to do in the Some case (α → R)
    produces a result (R)"

CONSTRUCTORS:

none : ∀A. Option A
none = ΛA. ΛR. λn:R. λs:A→R. n
  "To construct None: take the continuations, return the none-case"

some : ∀A. A → Option A
some = ΛA. λx:A. ΛR. λn:R. λs:A→R. s x
  "To construct Some x: take the continuations, call some-case with x"

ELIMINATOR:

matchOption : ∀A. ∀R. Option A → R → (A → R) → R
matchOption = ΛA. ΛR. λopt:(Option A). λn:R. λs:A→R. opt [R] n s
  "To match an option: just call it with the continuations!"

EXERCISE: Implement these three functions.
-}

-- optionType :: Type -> Type
-- optionType a = undefined
--   HINT: TyForall "R" (TyArr (TyVar "R") (TyArr (TyArr a (TyVar "R")) (TyVar "R")))

-- none :: Term
-- none = undefined
--   HINT: TyAbs "A" $ TyAbs "R" $ Lam "n" (TyVar "R") $ Lam "s" (TyArr (TyVar "A") (TyVar "R")) $ Var "n"

-- some :: Term
-- some = undefined

-- matchOption :: Term
-- matchOption = undefined

{- Exercise 1b: Either Type

DEFINITION:
  data Either α β = Left α | Right β

ENCODING:
  Either α β = ∀R. (α → R) → (β → R) → R

  Reading: "An either is a value that, given:
    - what to do with a left value (α → R)
    - what to do with a right value (β → R)
    chooses one and produces a result (R)"

CONSTRUCTORS:

left : ∀A. ∀B. A → Either A B
left = ΛA. ΛB. λx:A. ΛR. λl:A→R. λr:B→R. l x

right : ∀A. ∀B. B → Either A B
right = ΛA. ΛB. λy:B. ΛR. λl:A→R. λr:B→R. r y

ELIMINATOR:

matchEither : ∀A. ∀B. ∀R. Either A B → (A → R) → (B → R) → R
matchEither = ΛA. ΛB. ΛR. λe:(Either A B). λl:A→R. λr:B→R. e [R] l r

EXERCISE: Implement these functions.
-}

-- eitherType :: Type -> Type -> Type
-- eitherType a b = undefined

-- eitherLeft :: Term
-- eitherLeft = undefined

-- eitherRight :: Term
-- eitherRight = undefined

-- matchEither :: Term
-- matchEither = undefined

{- WHY CHURCH ENCODINGS?

ADVANTAGES:
1. No need to extend syntax with new types
2. Works in pure System F
3. Demonstrates expressive power
4. Used in proof assistants (Coq, Agda)

DISADVANTAGES:
1. Less efficient (extra function calls)
2. Harder to read and debug
3. Type inference becomes harder
4. Pattern matching is less convenient

PRACTICAL NOTE:
Real languages (Haskell, OCaml, Rust) use native ADTs for efficiency.
Church encodings are mainly theoretical interest.
-}

-- =============================================================================
-- Exercise 2: Polymorphic Data Structures (Medium)
-- =============================================================================

{- Exercise 2: Binary Trees

DEFINITION:
  data Tree α = Leaf | Node α (Tree α) (Tree α)

ENCODING:
  Tree α = ∀R. R → (α → R → R → R) → R

  Reading: "A tree is a value that, given:
    - what to do at a leaf (R)
    - what to do at a node (α → R → R → R)
    produces a result (R)"

CONSTRUCTORS:

leaf : ∀A. Tree A
leaf = ΛA. ΛR. λl:R. λn:A→R→R→R. l

node : ∀A. A → Tree A → Tree A → Tree A
node = ΛA. λx:A. λleft:(Tree A). λright:(Tree A).
  ΛR. λl:R. λn:A→R→R→R.
  n x (left [R] l n) (right [R] l n)

  Explanation:
  - ΛA: Abstract over element type
  - λx:A: Take the value for this node
  - λleft, λright: Take the subtrees
  - ΛR: Abstract over result type (for the eliminator)
  - λl, λn: Take the continuations
  - n x ...: Call node-continuation with:
      * x: this node's value
      * (left [R] l n): recursively fold left subtree
      * (right [R] l n): recursively fold right subtree

OPERATIONS:

treeMap : ∀A. ∀B. (A → B) → Tree A → Tree B
  Apply a function to every value in the tree.

  STRATEGY:
  - Type abstract over A and B
  - Take function f : A → B
  - Take tree : Tree A
  - Fold the tree with:
      * Leaf case: produce a leaf
      * Node case: apply f to value, recursively map subtrees

treeFold : ∀A. ∀B. B → (A → B → B → B) → Tree A → B
  Reduce a tree to a single value.

  STRATEGY:
  - Type abstract over A (element) and B (result)
  - Take base case: z : B (for leaves)
  - Take combining function: f : A → B → B → B
  - Take tree : Tree A
  - Just call the tree with [B] z f
    (This is the beauty of Church encoding!)

treeHeight : ∀A. Tree A → Nat
  Compute the height of a tree.

  STRATEGY:
  - Fold with:
      * Leaf case: 0
      * Node case: λx. λlh. λrh. succ (max lh rh)

EXERCISE: Implement these functions.
-}

-- treeType :: Type -> Type
-- treeType a = undefined

-- treeLeaf :: Term
-- treeLeaf = undefined

-- treeNode :: Term
-- treeNode = undefined
--   HINT: This one is complex! Follow the type carefully.

-- treeMap :: Term
-- treeMap = undefined

-- treeFold :: Term
-- treeFold = undefined
--   HINT: This is surprisingly simple with Church encoding!

-- treeHeight :: Term
-- treeHeight = undefined

-- =============================================================================
-- Exercise 3: Church Numerals Extended (Medium)
-- =============================================================================

{- Exercise 3: Arithmetic on Church Numerals

CHURCH NUMERAL ENCODING:
  CNat = ∀A. (A → A) → A → A

  Reading: "A number n is a value that applies a function n times."

EXAMPLES:
  zero = ΛA. λs:A→A. λz:A. z
    (Apply s zero times: just return z)

  one = ΛA. λs:A→A. λz:A. s z
    (Apply s once)

  two = ΛA. λs:A→A. λz:A. s (s z)
    (Apply s twice)

  three = ΛA. λs:A→A. λz:A. s (s (s z))
    (Apply s three times)

BASIC OPERATIONS (provided in Solutions.hs):

succ : CNat → CNat
succ = λn:CNat. ΛA. λs:A→A. λz:A. s (n [A] s z)
  "One more application of s"

add : CNat → CNat → CNat
add = λm:CNat. λn:CNat. ΛA. λs:A→A. λz:A. m [A] s (n [A] s z)
  "Apply s m times, starting from (s applied n times)"

mult : CNat → CNat → CNat
mult = λm:CNat. λn:CNat. ΛA. λs:A→A. λz:A. m [A] (n [A] s) z
  "Apply (n [A] s) a total of m times"
  "If n [A] s means 'apply s n times', then doing that m times means m×n applications"
-}

{- Exercise 3a: Exponentiation

TASK: Implement exp : CNat → CNat → CNat
      exp m n should compute m^n

HINT: Think about the pattern in mult!
  mult m n = m [A] (n [A] s) z
    "Apply the function (n [A] s) exactly m times"

For exponentiation:
  exp m n = ?

INSIGHT:
  2^3 = 2 × 2 × 2

  If we have mult : CNat → CNat → CNat, then:
    (mult 2) : CNat → CNat  (partially applied)

  We want to apply (mult m) to itself n times, starting from one:
    exp m n = n [CNat] (mult m) one

EXERCISE: Implement this!
-}

-- cnatExp :: Term
-- cnatExp = undefined
--   HINT: Use TyApp with cnatType

{- Exercise 3b: Factorial

TASK: Implement fact : CNat → CNat
      fact n should compute n!

CHALLENGE: This requires recursion!

In untyped lambda calculus, we use the Y combinator:
  Y = λf. (λx. f (x x)) (λx. f (x x))

But in System F, this doesn't type check! (Self-application x x fails.)

SOLUTION: We need a typed fixed-point combinator.
Unfortunately, this requires extending System F with a fix operator:

  fix : ∀A. (A → A) → A
  fix [A] f → f (fix [A] f)

With fix, factorial becomes:
  fact = fix [CNat → CNat]
           (λf:CNat→CNat. λn:CNat.
              if (iszero n) then one
              else (mult n (f (pred n))))

SIMPLIFIED VERSION:
For this exercise, just demonstrate the type by returning the argument:
  fact = λn:CNat. n

(A real implementation would need fix or recursive types.)
-}

-- cnatFactorial :: Term
-- cnatFactorial = undefined
--   HINT: For demonstration: Lam "n" cnatType (Var "n")

{- Exercise 3c: Division (Saturating)

TASK: Implement div : CNat → CNat → CNat
      div m n computes floor(m / n), returning 0 if n = 0

CHALLENGE: This also requires recursion!

STRATEGY (with fix):
  div = fix [CNat → CNat → CNat]
          (λdiv'. λm. λn.
             if (lt m n) then zero
             else succ (div' (sub m n) n))

For this exercise: Just return zero as a placeholder.
-}

-- cnatDiv :: Term
-- cnatDiv = undefined

{- REFLECTION: Why are these hard?

Church numerals are elegant for simple operations (succ, add, mult)
but complex operations (pred, sub, div) are very difficult!

REASON: Church numerals are "iteration" - they apply a function n times.
This works great for operations built from iteration.
But operations requiring inspection (is this zero?) are hard.

ALTERNATIVE: Scott encoding
  Nat = ∀R. R → (Nat → R) → R
  (Like Church encoding for data types, not numbers)

With Scott encoding, pred is easy:
  pred = λn. n [Nat] zero (λp. p)

But now addition is harder!

TRADEOFF: Different encodings optimize different operations.
-}

-- =============================================================================
-- Exercise 4: Existential Types (Hard)
-- =============================================================================

{- Exercise 4: Existential Types via Universal Encoding

INTUITION:
  ∃α. τ  means "there exists some type α such that we have τ"

Example:
  ∃State. (State, State → State, State → Int)

  This is an ABSTRACT DATA TYPE with:
  - Hidden representation type (State)
  - Initial state : State
  - update : State → State
  - query : State → Int

The client can use these operations but cannot inspect State directly.
This is the foundation of data abstraction!

ENCODING IN SYSTEM F:
  ∃α. τ  ≡  ∀R. (∀α. τ → R) → R

  Reading: "To have an existential, I can produce an R for any R,
            given a way to produce R from α (without knowing α)."

OPERATIONS:

pack : ∀A. τ → (∃A. τ)
pack = ΛA. λx:τ. ΛR. λf:(∀A. τ → R). f [A] x
  "Package a value with its hidden type"

unpack : (∃A. τ) → ∀R. (∀A. τ → R) → R
unpack = λpkg:(∃A. τ). ΛR. λf:(∀A. τ → R). pkg [R] f
  "Open a package by providing a continuation"

EXERCISE: Implement the existential encoding.
-}

-- existentialType :: Type -> Type
-- existentialType bodyTy = undefined
--   HINT: TyForall "R" (TyArr (TyForall "A" (TyArr bodyTy (TyVar "R"))) (TyVar "R"))

-- existentialPack :: Type -> Term
-- existentialPack bodyTy = undefined

-- existentialUnpack :: Type -> Term
-- existentialUnpack bodyTy = undefined

{- Exercise 4b: Abstract Counter ADT

TASK: Implement a counter ADT with hidden state.

INTERFACE:
  Counter = ∃State. { new : State,
                      inc : State → State,
                      get : State → Nat }

IMPLEMENTATION (using Nat as hidden type):
  new = 0
  inc = succ
  get = id

ENCODING AS NESTED PAIRS:
  Counter = ∃State. (State × (State → State) × (State → Nat))

The pack operation should:
1. Choose State = Nat (but this is hidden from clients!)
2. Package (0, succ, id) as the implementation

EXERCISE: Implement makeCounter.

CLIENT USAGE:
  unpack counter as <State, {new, inc, get}> in
    get (inc (inc new))

  Result: 2

  Note: Client never sees that State = Nat!
-}

-- makeCounter :: Term
-- makeCounter = undefined
--   HINT: Use existentialPack with appropriate tuple

{- WHY EXISTENTIALS MATTER:

1. DATA ABSTRACTION:
   Hide implementation details from clients.
   Example: Different counter implementations (Int vs Array)

2. MODULARITY:
   Change representation without changing client code.

3. TYPE SAFETY:
   Cannot mix values from different abstract types.
   Example: Counter1 ≠ Counter2 even if both use Nat

4. THEORETICAL IMPORTANCE:
   Connection to universal types (∀ and ∃ are dual).
   Used in encoding ML modules in System F.

5. MODERN LANGUAGES:
   - Haskell: ExistentialQuantification extension
   - OCaml: First-class modules
   - Rust: Trait objects
   - TypeScript: Existential types (limited)
-}

-- =============================================================================
-- Exercise 6: Impredicativity (Hard)
-- =============================================================================

{- Exercise 6: Impredicative Polymorphism

DEFINITION:
System F is IMPREDICATIVE: you can quantify over ALL types,
including polymorphic types.

∀α. τ  ranges over ALL types, including types like ∀β. β → β

This is different from PREDICATIVE systems where:
- Level 0: Base types (Nat, Bool)
- Level 1: Types of level-0 values (Nat → Bool)
- Level 2: Types of level-1 values (∀α. α → α)
- etc.

In predicative systems: ∀α. τ only ranges over types at level < n

WHY IMPREDICATIVITY MATTERS:
1. Self-application of polymorphic functions
2. More expressive encodings
3. Simpler type system (no levels)

WHY IT'S TRICKY:
1. Type inference becomes undecidable
2. Can lead to logical paradoxes (in dependent types)
3. Most modern languages restrict it (Haskell, Rust)
-}

{- Exercise 6a: Self-Application

TASK: Apply a polymorphic identity function to itself.

id : ∀A. A → A
id = ΛA. λx:A. x

Self-application:
  id [∀A. A → A] id

Type derivation:
  id : ∀A. A → A
  id [∀A. A → A] : (∀A. A → A) → (∀A. A → A)
  id [∀A. A → A] id : ∀A. A → A

This works because we can instantiate A with ∀A. A → A !
In predicative systems, this would be forbidden.

EXERCISE: Implement selfApply.
-}

-- polyId :: Term
-- polyId = undefined
--   HINT: TyAbs "A" $ Lam "x" (TyVar "A") (Var "x")

-- selfApply :: Term
-- selfApply = undefined
--   HINT: App (TyApp polyId (TyForall "A" (TyArr (TyVar "A") (TyVar "A")))) polyId

{- Exercise 6b: Nested Polymorphism

TASK: Define a function that takes a polymorphic argument.

twice : ∀A. (A → A) → A → A
twice = ΛA. λf:A→A. λx:A. f (f x)

polyTwice : (∀A. A → A) → (∀B. B → B)
polyTwice = λf:(∀A. A→A). ΛB. λx:B. twice [B] (f [B]) x

Note the type: Takes a POLYMORPHIC function, returns a POLYMORPHIC function.
This is rank-2 polymorphism (polymorphic argument).

Hindley-Milner cannot express this type!

EXERCISE: Implement twice and polyTwice.
-}

-- twice :: Term
-- twice = undefined

-- polyTwice :: Term
-- polyTwice = undefined
--   HINT: Note how f [B] instantiates the argument before passing to twice

{- RANK OF POLYMORPHISM:

Rank-0: No polymorphism
  Int → Int

Rank-1: Prenex polymorphism (∀ at top level)
  ∀A. A → A
  ∀A. ∀B. A → B → A
  This is what Hindley-Milner supports.

Rank-2: One level of nesting
  (∀A. A → A) → Int
  ∀B. (∀A. A → A) → B → B

Rank-3: Two levels of nesting
  ((∀A. A → A) → Int) → Bool

Rank-n: Arbitrary nesting

System F supports rank-∞ (arbitrary nesting).
Haskell with RankNTypes supports rank-n.
-}

-- =============================================================================
-- Exercise 7: System F Limitations and Parametricity (Hard)
-- =============================================================================

{- Exercise 7: Understanding Parametricity

REYNOLDS' PARAMETRICITY THEOREM:
Polymorphic functions must treat all types uniformly.
They cannot inspect types or branch based on types.

CONSEQUENCES:

1. FREE THEOREMS:
   The type alone severely constrains what a function can do.

   Examples:
   - f : ∀α. α → α  MUST be identity
     Proof: Cannot construct new α values, cannot drop input

   - f : ∀α. ∀β. α → β  is impossible
     Proof: Cannot construct β from nothing

   - f : ∀α. List α → List α  can only rearrange/duplicate/drop
     Cannot: modify elements, create new elements

   - f : ∀α. ∀β. (α → β) → List α → List β  must be map-like
     Proof: Only way to produce β is by calling the function

2. CANNOT IMPLEMENT:
   - Type case: (branch on whether α = Nat or α = Bool)
   - Generic equality: eq : ∀α. α → α → Bool
   - Generic show: show : ∀α. α → String
   - Generic comparison: compare : ∀α. α → α → Ordering

3. MODULARITY:
   Clients cannot break abstraction barriers.
   If you hide a type with ∃, clients cannot forge values.

EXERCISE: Write explanations for these limitations.
(See Solutions.hs for detailed explanations)
-}

{- SYSTEM F LIMITATIONS:

1. RECURSIVE TYPES:
   Pure System F cannot define recursive types like:
     List α = Unit + (α × List α)

   Need: μ-types (iso-recursive or equi-recursive)
     μα. τ

2. TYPE OPERATORS (need System F-omega):
   Cannot abstract over type constructors:
     Functor : (* → *) → *

   Need: Higher-kinded types (kinds)

3. DEPENDENT TYPES:
   Cannot have types depend on values:
     Vec : Nat → Type → Type
     Vec n α = length-n vector of α

   Need: Dependent type systems (Chapters 7-8!)

4. TYPE INFERENCE:
   Full type inference is undecidable (Wells 1999).
   Must provide type annotations.

   Solution: Bidirectional type checking, local inference

5. PRACTICAL EFFICIENCY:
   Type abstraction/application has runtime cost.
   Church encodings are slower than native data types.

   Solution: Type erasure, monomorphization
-}

-- =============================================================================
-- Testing Your Solutions
-- =============================================================================

{-
To test your implementations:

1. Load in GHCi:
   $ stack ghci
   > :load exercises/Hints.hs

2. Test Church encodings:
   > :load exercises/Solutions.hs
   > let x = App (TyApp some TyNat) (TmSucc TmZero)
   > -- Evaluate to see Some(1)

3. Test parametricity:
   Try implementing: ∀α. α → α that's NOT identity
   (You cannot!)

4. Compare with Hindley-Milner:
   Load chapter-04 and note the differences in expressiveness.

5. Run the test suite:
   $ stack test
-}

-- =============================================================================
-- Common Mistakes
-- =============================================================================

{-
1. FORGETTING TYPE APPLICATIONS
   ✗ App some (TmSucc TmZero)
   ✓ App (TyApp some TyNat) (TmSucc TmZero)

   In System F, type application is EXPLICIT!

2. WRONG ORDER OF ABSTRACTIONS
   ✗ λx:A. ΛA. ...  (A is not in scope!)
   ✓ ΛA. λx:A. ...  (Type abstraction comes first)

3. CONFUSING ∀ AND ∃
   ∀α. τ : "For all types α, I can provide τ"
   ∃α. τ : "There exists some type α such that I have τ"

   ∀ is provider's choice (function chooses)
   ∃ is caller's choice (caller knows the type)

4. EXPECTING TYPE INFERENCE
   System F requires annotations!
   Unlike Hindley-Milner, you cannot omit types.

5. BREAKING PARAMETRICITY
   ✗ Trying to implement: ∀α. α → α → Bool
   This would require inspecting α, which is impossible!

6. CHURCH ENCODING MISTAKES
   Make sure the eliminator arguments match the encoding.
   Option: R → (α → R) → R
   Not: (α → R) → R → R  (order matters!)
-}

-- =============================================================================
-- Further Reading
-- =============================================================================

{-
Papers:
- Girard (1972): "Interprétation fonctionnelle et élimination des coupures"
  Original System F paper (independently discovered by Reynolds)

- Reynolds (1974): "Towards a theory of type structure"
  System F from a PL perspective

- Reynolds (1983): "Types, Abstraction and Parametric Polymorphism"
  Parametricity theorem and free theorems

- Wadler (1989): "Theorems for free!"
  Making parametricity practical

- Wells (1999): "Typability and type checking in System F are equivalent and undecidable"
  Proof that type inference is undecidable

Books:
- Girard, Lafont, Taylor: "Proofs and Types"
  Deep dive into System F and proof theory

- Pierce, TAPL: Chapter 23 (Universal Types), Chapter 24 (Existential Types)

- Barendregt: "Lambda Calculi with Types"
  The comprehensive reference

Next Steps:
- Chapter 6: System F-omega (higher-kinded types)
- Chapter 7: Dependent types (types depending on values!)
- Chapter 8: Full dependent types with universe hierarchy
-}
