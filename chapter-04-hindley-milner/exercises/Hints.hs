{-# LANGUAGE LambdaCase #-}

module Hints where

import Syntax
import Infer
import Eval

{-|
CHAPTER 4 EXERCISE HINTS

This file provides scaffolding and hints for Chapter 4 exercises.
Try implementing solutions yourself before looking at Solutions.hs!

Chapter 4 introduces Hindley-Milner type inference with let-polymorphism.
The KEY difference from STLC: you don't need to write type annotations!

MAJOR FEATURES:
- Automatic type inference (Algorithm W)
- Let-polymorphism (let-bound variables can be polymorphic)
- Type schemes (∀α. τ)
- Unification with occurs check

KEY INSIGHT: The difference between:
  let id = λx. x in ...     -- id has type ∀α. α → α
  (λid. ...) (λx. x)        -- id has type τ → τ (monomorphic)
-}

-- =============================================================================
-- Helper Functions (Provided)
-- =============================================================================

-- No special helpers needed - type inference handles most complexity!

-- =============================================================================
-- Exercise 1: Type Inference Practice (Easy)
-- =============================================================================

{- Exercise 1a: Function Composition

TASK: Implement compose without type annotations!

compose = λf. λg. λx. f (g x)

EXPECTED TYPE: (β → γ) → (α → β) → α → γ

HOW TYPE INFERENCE WORKS:
1. Generate fresh type variables: f : α₁, g : α₂, x : α₃
2. From (g x): α₂ = α₃ → α₄ (for some fresh α₄)
3. From (f (g x)): α₁ = α₄ → α₅ (for some fresh α₅)
4. Substitute and simplify: (α₄ → α₅) → (α₃ → α₄) → α₃ → α₅
5. Rename to canonical form: (β → γ) → (α → β) → α → γ

HINT: Just write the lambda term! The type checker will figure it out.
-}

-- compose :: Term
-- compose = undefined
--   HINT: Lam "f" $ Lam "g" $ Lam "x" $ App (Var "f") (App (Var "g") (Var "x"))

{- Exercise 1b: S Combinator

TASK: Implement the S combinator from combinatory logic.

s = λx. λy. λz. x z (y z)

EXPECTED TYPE: (α → β → γ) → (α → β) → α → γ

This is a classic example where type inference shines!
Try to derive the type manually first, then check your work.

DERIVATION HINT:
- x is applied to two arguments, so: x : α₁ → α₂ → α₃
- y is applied to one argument: y : α₄ → α₅
- z is used twice with different types... wait, can it be?
- Actually z must have the SAME type in both uses!
- Work backwards from the applications
-}

-- sCombinator :: Term
-- sCombinator = undefined

{- Exercise 1c: Twice

TASK: Apply a function twice to an argument.

twice = λf. λx. f (f x)

EXPECTED TYPE: (α → α) → α → α

KEY CONSTRAINT: The input and output types of f must be the SAME.
This is because f's output is fed back as f's input!

QUESTION: Could twice have type (α → β) → α → β?
Answer: No! Because we'd need β = α from the constraint that
        the first application's output matches the second application's input.
-}

-- twice :: Term
-- twice = undefined

{- Exercise 1d: Flip

TASK: Flip the order of arguments to a function.

flip = λf. λx. λy. f y x

EXPECTED TYPE: (α → β → γ) → β → α → γ

HINT: Note how the argument order changes from (α → β → γ) to β → α → ...
-}

-- flipFn :: Term
-- flipFn = undefined

-- =============================================================================
-- Exercise 2: Polymorphic List Operations (Medium)
-- =============================================================================

{- Exercise 2: List Operations

NOTE: The current implementation uses built-in lists with:
- TmNil : List α
- TmCons : α → List α → List α
- TmIsNil : List α → Bool
- TmHead : List α → α
- TmTail : List α → List α

These are simplified - in a real implementation, you'd need proper
pattern matching and fix for general recursion.

For these exercises, implement SIMPLIFIED versions that work for small
lists (up to length 3) to demonstrate the polymorphic types.
-}

{- Exercise 2a: Map

TASK: Apply a function to every element of a list.

EXPECTED TYPE: (α → β) → List α → List β

STRATEGY (for simplified version):
1. Check if list is empty → return empty
2. Otherwise, apply f to head, recursively map over tail
3. Cons the results together

SIMPLIFIED IMPLEMENTATION (for lists up to length 3):
map f list =
  if isnil list
  then nil
  else let h = head list in
       let t = tail list in
       cons (f h)
            (if isnil t then nil
             else cons (f (head t)) nil)

POLYMORPHISM: Notice that α and β can be DIFFERENT types!
Examples:
- map succ : List Nat → List Nat
- map (λx:Nat. x > 0) : List Nat → List Bool
-}

-- mapList :: Term
-- mapList = undefined

{- Exercise 2b: Filter

TASK: Keep only elements satisfying a predicate.

EXPECTED TYPE: (α → Bool) → List α → List α

STRATEGY:
- For each element, test the predicate
- If true: keep it
- If false: skip it

SIMPLIFIED VERSION:
filter pred list =
  if isnil list
  then nil
  else let h = head list in
       if (pred h)
       then cons h (... recursively filter tail ...)
       else (... recursively filter tail ...)
-}

-- filterList :: Term
-- filterList = undefined

{- Exercise 2c: Length

TASK: Count the number of elements.

EXPECTED TYPE: List α → Nat

KEY INSIGHT: The result type is always Nat, regardless of what α is!
This demonstrates parametricity - we don't care about the element type.

STRATEGY:
length list =
  if isnil list
  then 0
  else succ (length (tail list))
-}

-- lengthList :: Term
-- lengthList = undefined

{- Exercise 2d: FoldL (Left Fold)

TASK: Reduce a list from left to right.

EXPECTED TYPE: (β → α → β) → β → List α → β

INTUITION:
foldl (+) 0 [1,2,3] = ((0 + 1) + 2) + 3 = 6
                       ^^^^ β   ^^^^ accumulator
                             ^ α (list element)

STRATEGY:
foldl f z [] = z
foldl f z (x::xs) = foldl f (f z x) xs

For simplified version (small lists):
foldl f z list =
  if isnil list
  then z
  else f z (head list)  -- Just one step for demonstration
-}

-- foldlList :: Term
-- foldlList = undefined

{- Exercise 2e: FoldR (Right Fold)

TASK: Reduce a list from right to left.

EXPECTED TYPE: (α → β → β) → β → List α → β

INTUITION:
foldr (+) 0 [1,2,3] = 1 + (2 + (3 + 0)) = 6
                                    ^^^^ base
                           ^^^^ accumulator
                      ^ α (list element)

DIFFERENCE FROM FOLDL: Note the function type!
- foldl: (β → α → β) - accumulator comes first
- foldr: (α → β → β) - list element comes first

For simplified version:
foldr f z list =
  if isnil list
  then z
  else f (head list) z  -- Element comes first
-}

-- foldrList :: Term
-- foldrList = undefined

-- =============================================================================
-- Exercise 3: Let-Polymorphism vs Lambda (Medium)
-- =============================================================================

{- Exercise 3: The Key Difference in Hindley-Milner

THIS IS THE MOST IMPORTANT EXERCISE IN CHAPTER 4!

BACKGROUND:
In STLC (Chapter 2), we learned that:
  let x = t₁ in t₂  ≡  (λx. t₂) t₁

But in Hindley-Milner, this is NO LONGER TRUE!
Let-bindings are special: they allow polymorphism.

EXAMPLE THAT WORKS:
let id = λx. x
in pair (id 0) (id true)

Type derivation:
1. Infer type of λx. x : α → α (with free type variable α)
2. GENERALIZE to get type scheme: ∀α. α → α
3. Each use of 'id' can INSTANTIATE α differently:
   - (id 0) : Nat → Nat where α = Nat
   - (id true) : Bool → Bool where α = Bool
4. Result type: Nat × Bool ✓

EXAMPLE THAT FAILS:
(λid. pair (id 0) (id true)) (λx. x)

Type derivation:
1. Infer type of λx. x : α → α (with free type variable α)
2. This becomes the type of parameter 'id'
3. In the body, 'id' has type α → α (NOT generalized!)
4. First use (id 0) requires: α = Nat
5. Second use (id true) requires: α = Bool
6. Unification fails: Nat ≠ Bool ✗

KEY RULE:
- LET-BOUND variables: type is GENERALIZED (∀α. τ)
- LAMBDA-BOUND variables: type is NOT generalized (τ)
-}

{- Exercise 3a: Demonstrate Let-Polymorphism

TASK: Write the term that SHOULD type check.

letPolymorphic =
  let id = λx. x
  in pair (id 0) (id true)

EXPECTED TYPE: Nat × Bool

WHAT TO IMPLEMENT:
Use the Let constructor (not lambda!) to bind 'id'.
-}

-- letPolymorphic :: Term
-- letPolymorphic = undefined
--   HINT: Let "id" (Lam "x" (Var "x"))
--           (TmPair (App (Var "id") TmZero)
--                   (App (Var "id") TmTrue))

{- Exercise 3b: Demonstrate Lambda Monomorphism

TASK: Write the term that SHOULD fail to type check.

lambdaMonomorphic =
  (λid. pair (id 0) (id true)) (λx. x)

EXPECTED: Type error (unification failure)

WHAT TO IMPLEMENT:
Use the Lam constructor to bind 'id' as a lambda parameter.

TRY IT:
After implementing, run:
  > inferType emptyCtx lambdaMonomorphic

You should get a type error!
-}

-- lambdaMonomorphic :: Term
-- lambdaMonomorphic = undefined
--   HINT: App (Lam "id" (TmPair (App (Var "id") TmZero)
--                                (App (Var "id") TmTrue)))
--             (Lam "x" (Var "x"))

{- CHALLENGE QUESTIONS:

1. Can you have polymorphism with lambda in System F (Chapter 5)?
   Hint: Yes, but you need explicit type abstractions (ΛA. ...)!

2. Why does Hindley-Milner restrict polymorphism to let?
   Answer: To make type inference DECIDABLE!

   If lambda-bound variables could be polymorphic, we'd need to guess
   which type variables to generalize, making inference undecidable.

3. Can you implement let-polymorphism in terms of lambda + System F?
   Answer: Yes! let x = t₁ in t₂ desugars to:
           (ΛA. λx:A. t₂) [infer(t₁)] t₁
           where we explicitly abstract over type variables.
-}

-- =============================================================================
-- Exercise 5: Polymorphic Trees (Medium)
-- =============================================================================

{- Exercise 5: Binary Trees with Polymorphism

For these exercises, we use a simplified encoding with booleans:
- Leaf: true
- Node: (false, (value, true))  -- Simplified structure

In a real implementation, you'd use proper ADTs or Church encoding.

These exercises demonstrate polymorphic recursion and type inference.
-}

{- Exercise 5a: Tree Map

TASK: Apply a function to every value in a tree.

EXPECTED TYPE: (α → β) → Tree α → Tree β

STRATEGY (for real implementation):
treeMap f tree =
  match tree with
  | Leaf -> Leaf
  | Node(v, l, r) -> Node(f v, treeMap f l, treeMap f r)

SIMPLIFIED VERSION:
Just return the input tree to demonstrate the type.
-}

-- treeMap :: Term
-- treeMap = undefined
--   HINT: For simplified version: Lam "f" $ Lam "tree" $ Var "tree"

{- Exercise 5b: Tree Fold

TASK: Reduce a tree to a single value.

EXPECTED TYPE: β → (α → β → β → β) → Tree α → β

INTUITION:
treeFold leafVal nodeF tree =
  match tree with
  | Leaf -> leafVal
  | Node(v, l, r) -> nodeF v (treeFold leafVal nodeF l)
                              (treeFold leafVal nodeF r)

EXAMPLE:
To sum a tree of numbers:
  treeFold 0 (λx. λl. λr. x + l + r) tree
-}

-- treeFold :: Term
-- treeFold = undefined

{- Exercise 5c: Tree Height

TASK: Compute the height of a tree.

EXPECTED TYPE: Tree α → Nat

KEY INSIGHT: The result is Nat regardless of element type!
This demonstrates parametricity.

STRATEGY:
height tree =
  match tree with
  | Leaf -> 0
  | Node(_, l, r) -> 1 + max (height l) (height r)
-}

-- treeHeight :: Term
-- treeHeight = undefined

-- =============================================================================
-- Testing Your Solutions
-- =============================================================================

{-
To test your implementations:

1. Load in GHCi:
   $ stack ghci
   > :load exercises/Hints.hs

2. Test type inference:
   > inferType emptyCtx compose
   Should print: (β → γ) → (α → β) → α → γ

3. Check let-polymorphism:
   > inferType emptyCtx letPolymorphic
   Should succeed!

   > inferType emptyCtx lambdaMonomorphic
   Should fail with unification error!

4. Run the test suite:
   $ stack test
-}

-- =============================================================================
-- Understanding Algorithm W
-- =============================================================================

{-
Hindley-Milner type inference uses Algorithm W (for "Wrong" because it
computes types left-to-right, which seems backwards).

ALGORITHM W STEPS:
1. Assign fresh type variables to unknowns
2. Generate constraints from the term structure
3. Unify constraints using Robinson's unification algorithm
4. Substitute solutions back into the type
5. Generalize free type variables at let-bindings

EXAMPLE: Infer type of (λf. λx. f (f x))

Step 1: Assign fresh variables
  f : α₁
  x : α₂

Step 2: Generate constraints
  From (f x):
    α₁ = α₂ → α₃  (for fresh α₃)
  From f (f x):
    α₁ = α₃ → α₄  (for fresh α₄)

Step 3: Unify
  α₁ = α₂ → α₃
  α₁ = α₃ → α₄

  Substitute first into second:
  α₂ → α₃ = α₃ → α₄

  Unify components:
  α₂ = α₃
  α₃ = α₄

  Therefore: α₂ = α₃ = α₄

Step 4: Substitute
  α₁ = α₂ → α₂

Step 5: Final type
  (α₂ → α₂) → α₂ → α₂

  Rename to canonical:
  (α → α) → α → α

OCCURS CHECK:
When unifying α = τ, we must check that α doesn't occur in τ.
Otherwise we'd have infinite types like: α = α → α

Example of occurs check failure:
  (λx. x x)

  Constraint: α = α → β
  Occurs check: α occurs in α → β
  Result: TYPE ERROR ✗
-}

-- =============================================================================
-- Let-Polymorphism vs System F
-- =============================================================================

{-
COMPARISON TABLE:

╔═══════════════════╦═══════════════════════╦═══════════════════════╗
║                   ║  Hindley-Milner       ║  System F             ║
╠═══════════════════╬═══════════════════════╬═══════════════════════╣
║ Type Inference    ║  Automatic            ║  Requires annotations ║
║ Polymorphism      ║  Let-bound only       ║  Explicit (ΛA. ...)   ║
║ Type Application  ║  Implicit             ║  Explicit ([τ])       ║
║ Expressiveness    ║  Less (predicative)   ║  More (impredicative) ║
║ Decidability      ║  Decidable            ║  Undecidable          ║
║ Real Languages    ║  ML, Haskell (98)     ║  Haskell (extensions) ║
╚═══════════════════╩═══════════════════════╩═══════════════════════╝

KEY INSIGHT:
Hindley-Milner trades expressiveness for decidability.
You can't write all System F programs, but you get automatic inference!

EXAMPLE OF HM LIMITATION:
Cannot express: (∀A. A → A) → Int

In System F:
  λf:(∀A. A → A). f [Int] 42

In Hindley-Milner:
  Not expressible!
  Functions cannot take polymorphic arguments.
  This is called "rank-1 polymorphism" or "prenex polymorphism".
-}

-- =============================================================================
-- Common Mistakes
-- =============================================================================

{-
1. CONFUSING LET AND LAMBDA
   ✗ (λx. ...) where you need polymorphism
   ✓ let x = ... in ... for polymorphism

2. EXPECTING LAMBDA-BOUND POLYMORPHISM
   ✗ (λid. id 0, id true) (λx. x)
   ✓ let id = λx. x in (id 0, id true)

3. FORGETTING OCCURS CHECK
   Example: λx. x x
   This seems like it should work, but it requires infinite types!

4. OVER-GENERALIZATION
   Don't generalize type variables that escape their scope.
   Example:
     let f = λx. x in
     let y = f 0 in
     f true  -- OK, f is still polymorphic

   vs.

     (λf. let y = f 0 in f true) (λx. x)  -- ERROR
     Here f is not polymorphic (lambda-bound)

5. EXPECTING HIGHER-RANK TYPES
   ✗ λf:(∀A. A → A). ...
   Hindley-Milner cannot express this.
   You need System F or rank-n types extension.
-}

-- =============================================================================
-- Further Reading
-- =============================================================================

{-
Papers:
- Damas & Milner (1982): "Principal type-schemes for functional programs"
  The original paper on Algorithm W

- Hindley (1969): "The Principal Type-Scheme of an Object in Combinatory Logic"
  Earlier work on type inference

- Robinson (1965): "A Machine-Oriented Logic Based on the Resolution Principle"
  Unification algorithm

Books:
- Pierce, TAPL: Chapter 22 (Type Reconstruction)
- Harper, PFPL: Chapter 19 (Type Inference)

Modern Extensions:
- Rank-N Types (allows polymorphic function arguments)
- GADTs (Generalized Algebraic Data Types)
- Type Families (type-level computation)
- Dependent Types (Chapter 7-8 of this course!)
-}
