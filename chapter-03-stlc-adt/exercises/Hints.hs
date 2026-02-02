{-# LANGUAGE LambdaCase #-}

module Hints (module Hints) where

import Syntax

{-|
CHAPTER 3 EXERCISE HINTS

This file provides scaffolding and hints for Chapter 3 exercises.
Try implementing solutions yourself before looking at Solutions.hs!

Chapter 3 has FULL support for ADTs, so all exercises can be implemented!
-}

-- =============================================================================
-- Helper Functions (Provided)
-- =============================================================================

-- | Convert Int to natural number Term
natFromInt :: Int -> Term
natFromInt 0 = TmZero
natFromInt n = TmSucc (natFromInt (n - 1))

-- | Convert Term back to Int (if it's a natural number)
termToInt :: Term -> Maybe Int
termToInt TmZero = Just 0
termToInt (TmSucc t) = fmap (+1) (termToInt t)
termToInt _ = Nothing

-- =============================================================================
-- Exercise 1: List Operations (Easy)
-- =============================================================================

{- Exercise 1a: Append

HINT: Think recursively on the first list.

Base case: append [] ys = ys
Recursive case: append (x::xs) ys = x :: (append xs ys)

IMPLEMENTATION STRATEGY:
Use pattern matching (TmMatch) with two cases:
1. If first list is nil → return second list
2. If first list is (x::xs) → cons x onto (append xs ys)

COMMON PITFALL: Forgetting the type annotation on TmNil
✗ TmNil
✓ TmNil someType
-}

-- append :: Type -> Term
-- append elemType = undefined
--   HINT: Return a lambda that takes two lists
--   λxs. λys. match xs with
--     | [] -> ys
--     | (h::t) -> h :: (append elemType t ys)

{- Exercise 1b: Reverse

HINT: Use a helper function with an accumulator!

reverse_helper xs acc = match xs with
  | [] -> acc
  | (h::t) -> reverse_helper t (h::acc)

reverse xs = reverse_helper xs []

WHY ACCUMULATOR? Direct reversal would be O(n²).
With accumulator: O(n)

ALTERNATIVE: Use append, but that's less efficient.
-}

-- reverseList :: Type -> Term
-- reverseList elemType = undefined

{- Exercise 1c: Length

HINT: Count elements using recursion.

length xs = match xs with
  | [] -> 0
  | (h::t) -> succ (length t)

Type: List τ → Nat

REMEMBER: The result is always Nat, regardless of list element type!
-}

-- lengthList :: Type -> Term
-- lengthList elemType = undefined

-- =============================================================================
-- Exercise 2: Binary Trees (Medium)
-- =============================================================================

{- Exercise 2a: Tree Definition

HINT: Use variant types!

Tree τ = <leaf: Unit, node: τ × Tree τ × Tree τ>

A tree is EITHER:
- A leaf (contains Unit)
- A node (contains value + left subtree + right subtree)

EXAMPLE:
    5
   / \
  3   7

Would be represented as:
<node=(5, <node=(3, <leaf=()>, <leaf=()>)>,
           <node=(7, <leaf=()>, <leaf=()>)>)>
-}

-- Helper: Create the tree type
-- treeType :: Type -> Type
-- treeType elemType = undefined
--   HINT: TyVariant with "leaf" and "node" labels

-- Helper: Create a leaf
-- leaf :: Type -> Term
-- leaf elemType = undefined
--   HINT: TmTag "leaf" TmUnit (treeType elemType)

-- Helper: Create a node
-- node :: Type -> Term -> Term -> Term -> Term
-- node elemType value left right = undefined
--   HINT: TmTag "node" (TmPair value (TmPair left right)) (treeType elemType)

{- Exercise 2b: Tree Operations

HEIGHT:
HINT: Use pattern matching on the variant.

height tree = match tree with
  | <leaf=_> -> 0
  | <node=(v, (l, r))> -> 1 + max (height l) (height r)

MIRROR:
HINT: Swap left and right subtrees recursively.

mirror tree = match tree with
  | <leaf=u> -> <leaf=u>
  | <node=(v, (l, r))> -> <node=(v, (mirror r, mirror l))>
                                        ^swap^

MAP:
HINT: Apply function to node values, recursively to subtrees.

map f tree = match tree with
  | <leaf=u> -> <leaf=u>
  | <node=(v, (l, r))> -> <node=(f v, (map f l, map f r))>
-}

-- =============================================================================
-- Exercise 3: Option Type (Medium)
-- =============================================================================

{- Exercise 3: Option Type

ENCODING: Option τ = Unit + τ

none = inl[()] () : Unit + τ
some x = inr[Unit] x : Unit + τ

HINT for map:
map f opt = case opt of
  | inl u -> inl u    (none stays none)
  | inr x -> inr (f x) (some x becomes some (f x))

HINT for bind:
bind opt f = case opt of
  | inl u -> inl u    (none stays none)
  | inr x -> f x       (some x becomes f x)

HINT for getOrElse:
getOrElse opt default = case opt of
  | inl u -> default
  | inr x -> x
-}

-- optionType :: Type -> Type
-- optionType elemType = TySum TyUnit elemType

-- none :: Type -> Term
-- none elemType = TmInl elemType TmUnit

-- some :: Term -> Term
-- some t = TmInr TyUnit t

-- =============================================================================
-- Exercise 4: Expression Evaluator (Hard)
-- =============================================================================

{- Exercise 4: Expression Evaluator

ENCODING:
Expr = <lit: Nat,
        add: Expr × Expr,
        mul: Expr × Expr,
        var: Nat>  -- Using de Bruijn indices

EVALUATOR STRATEGY:
1. Keep an environment (list of Nat values)
2. Match on expression type:
   - lit n -> just return n
   - add (e1, e2) -> eval e1 + eval e2
   - mul (e1, e2) -> eval e1 * eval e2
   - var i -> lookup i in environment

HINT for de Bruijn indices:
var 0 = most recently bound variable
var 1 = second most recent
etc.

OPTIMIZER HINTS:
Constant folding opportunities:
- add (lit m) (lit n) → lit (m+n)
- mul (lit 0) e → lit 0
- mul (lit 1) e → e
- mul e (lit 0) → lit 0
- mul e (lit 1) → e
-}

-- =============================================================================
-- Exercise 5: Record Operations (Medium)
-- =============================================================================

{- Exercise 5: Record Operations

UPDATE:
HINT: Create a new record with updated field.

updateX record newValue =
  {x = newValue, y = record.y}

In terms: TmRecord (Map.fromList [("x", newValue), ("y", TmProj record "y")])

MERGE:
HINT: Use Map.union to combine records.

merge r1 r2 = combine all fields from r1 and r2

In Haskell: Map.union (fields of r1) (fields of r2)

IMPORTANT: Make sure field names don't overlap!
-}

-- =============================================================================
-- Exercise 6: Exhaustiveness Checking (Hard)
-- =============================================================================

{- Exercise 6: Exhaustiveness Checking

TASK: Check if all constructors of a variant are covered.

STRATEGY:
1. Get all labels from variant type
2. Get all labels from patterns in case expression
3. Check: all variant labels appear in patterns?

EXAMPLE:
Type: <left: Nat, right: Bool>
Patterns: <left=x>, <right=y>
Result: EXHAUSTIVE ✓

Patterns: <left=x>
Result: NON-EXHAUSTIVE ✗ (missing <right>)

HINT: Use Set operations!
Set.fromList variantLabels `Set.isSubsetOf` Set.fromList patternLabels
-}

-- =============================================================================
-- Testing Hints
-- =============================================================================

{-
To test your implementations:

1. Load in GHCi:
   $ stack ghci
   > :load exercises/Hints.hs

2. Test individual functions:
   > let myList = TmCons (natFromInt 1) (TmCons (natFromInt 2) (TmNil TyNat))
   > eval (App (lengthList TyNat) myList)

3. Check types:
   > typeOf emptyCtx (append TyNat)

4. Run test suite:
   $ stack test
-}

-- =============================================================================
-- Common Mistakes to Avoid
-- =============================================================================

{-
1. FORGETTING TYPE ANNOTATIONS
   Lists and options need type annotations:
   ✗ TmNil
   ✓ TmNil TyNat

2. PATTERN MATCHING ORDER
   Put more specific patterns first!
   ✗ _ before specific patterns (will match everything)
   ✓ Specific patterns, then wildcard

3. RECURSIVE CALLS
   Make sure recursive calls get smaller arguments!
   Otherwise: infinite loop

4. CASE VS MATCH
   - TmCase: for sum types (binary)
   - TmCaseVariant: for variants (n-ary)
   - TmMatch: general pattern matching

5. DE BRUIJN INDICES
   Remember: 0 is most recent, not oldest!
   λx. λy. var 0 refers to y, not x
-}

-- =============================================================================
-- Further Reading
-- =============================================================================

{-
Pierce, TAPL:
- Chapter 11: Simple Extensions (products, sums, records, variants)
- Chapter 15: Recursive Types

Harper, PFPL:
- Chapter 10: Product and Sum Types
- Chapter 11: Pattern Matching
-}
