# Chapter 15: Recursive Types (μ Types) - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce recursive type concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Type Substitution ⭐
Perform the substitution for each recursive type:

a) `μα. Unit + α` → `T[μα.T/α]` = ?
b) `μα. Nat × α` → `T[μα.T/α]` = ?
c) `μα. (α × α) + Nat` → `T[μα.T/α]` = ?

### Problem 1.2: Identifying Fold/Unfold ⭐
For `NatList = μα. Unit + (Nat × α)`, which need fold or unfold?

a) Creating empty list
b) Adding element to front
c) Checking if list is empty
d) Getting first element

### Problem 1.3: Type Checking ⭐
Given `Tree = μα. Nat + (α × α)`, what are the types of:

a) `fold [Tree] (inl 5)`
b) `unfold [Tree] (fold [Tree] (inl 5))`
c) `fold [Tree] (inr <fold [Tree] (inl 1), fold [Tree] (inl 2)>)`

### Problem 1.4: Reading Recursive Types ⭐
What data structures do these represent?

a) `μα. Bool + (Bool × α)`
b) `μα. Unit + (Nat × α × α)`
c) `μα. (Nat × Nat) + (α × α)`

### Problem 1.5: Basic Constructors ⭐
For `Stream = μα. Nat × α`, write:

a) The type of the head element
b) The type after one unfold
c) A stream of all zeros (assume general recursion)

---

## Standard Problems (45-60 minutes)

### Problem 2.1: List Operations ⭐⭐
For `NatList = μα. Unit + (Nat × α)`, implement:

a) **append**: Concatenate two lists
b) **reverse**: Reverse a list
c) **map**: Apply function to all elements

Test cases:
- `append [1,2] [3,4]` → `[1,2,3,4]`
- `reverse [1,2,3]` → `[3,2,1]`
- `map succ [1,2,3]` → `[2,3,4]`

### Problem 2.2: Tree Operations ⭐⭐
For `Tree = μα. Nat + (α × α)`, implement:

a) **height**: Maximum depth of tree
b) **mirror**: Swap left and right subtrees
c) **flatten**: Convert tree to list (in-order)

Test with:
```
    *
   / \
  1   *
     / \
    2   3
```

### Problem 2.3: Alternative List Type ⭐⭐
Define a list type with head and optional tail:

a) Write the recursive type definition
b) Implement constructors (single, cons)
c) Implement `toNatList` converter

Compare with standard list encoding.

### Problem 2.4: Binary Search Tree ⭐⭐
For `BST = μα. Unit + (Nat × α × α)`:

a) Explain the structure
b) Write `insert : Nat → BST → BST`
c) Write `contains : Nat → BST → Bool`

### Problem 2.5: Mutual Recursion Encoding ⭐⭐
Encode mutually recursive types using nested μ:

```
-- Even and Odd natural numbers
Even = succ (Odd)
Odd = succ (Even)
```

a) Encode as nested recursive types
b) Write constructors
c) Explain the encoding

### Problem 2.6: Rose Trees ⭐⭐
A rose tree has a value and a list of children:

a) Define `RoseTree = μα. Nat × ???`
b) Implement constructors
c) Implement `depth : RoseTree → Nat`

Hint: You'll need a list type embedded in the definition.

### Problem 2.7: Polymorphic Lists ⭐⭐
Can we encode polymorphic lists with μ?

a) Try: `List α = μβ. Unit + (α × β)`
b) What's the issue?
c) How would full polymorphism help?

### Problem 2.8: Stream Operations ⭐⭐
For `Stream = μα. Nat × α`, implement:

a) **drop**: Skip first n elements
b) **zipWith**: Combine two streams elementwise
c) **iterate**: Generate stream from function

Example: `iterate succ 0` → `[0,1,2,3,...]`

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Y Combinator ⭐⭐⭐
Derive the typed Y combinator using recursive types:

a) Define `Fix = μα. (α → T) → T` for some T
b) Implement `fix : (T → T) → T`
c) Use it to define factorial
d) Explain why this breaks termination

### Problem 3.2: Coinductive Types ⭐⭐⭐
Compare inductive and coinductive interpretations:

a) `NatList` as inductive (finite lists)
b) `Stream` as coinductive (infinite streams)
c) What's the fundamental difference?
d) Can we have infinite lists with NatList?

### Problem 3.3: Sized Types ⭐⭐⭐
Add size information to recursive types:

a) Define `Vec (n:Nat) = μα. ???` (length-indexed vectors)
b) Can pure μ types express this?
c) What extension would you need?
d) Sketch how sized types work

### Problem 3.4: Scott Encoding ⭐⭐⭐
Compare Church and Scott encodings:

a) Church numerals: `Nat = ∀α. (α → α) → α → α`
b) Scott numerals: `Nat = μα. Unit + α`
c) Compare `pred` efficiency
d) Which is better for what?

### Problem 3.5: Equi-Recursive Semantics ⭐⭐⭐
Imagine implementing equi-recursive types:

a) What's the type equality rule?
b) How do you check `μα.T = T[μα.T/α]`?
c) What about `μα.T = μβ.T[β/α]`?
d) Why is this harder than iso-recursive?

### Problem 3.6: Negative Occurrences ⭐⭐⭐
Explore problematic recursive types:

a) Define `Bad = μα. α → Nat`
b) Try to construct a value of type Bad
c) What goes wrong?
d) Why do some systems allow this?

---

## Debugging Exercises (30 minutes)

### Debug 1: Missing Fold ⭐
What's wrong?

```
nil : NatList
nil = inl unit
```

Fix the code and explain.

### Debug 2: Missing Unfold ⭐
What's wrong?

```
head : NatList → Nat
head = λl.
  case l of
    inl _ => 0
  | inr p => fst p
```

Fix and explain.

### Debug 3: Wrong Type Annotation ⭐⭐
What's wrong?

```
NatList = μα. Unit + (Nat × α)
nil = fold [Unit + (Nat × NatList)] (inl unit)
```

Fix and explain.

### Debug 4: Evaluation Order ⭐⭐
Why doesn't this work in call-by-value?

```
ones : Stream
ones = fold [Stream] <1, ones>
```

How would you fix it?

### Debug 5: Type Mismatch ⭐⭐
Find the error:

```
Tree = μα. Nat + (α × α)
badTree : Tree
badTree = fold [Tree] <leaf 1, leaf 2>
```

What's the fix?

### Debug 6: Infinite Unfolding ⭐⭐
Why does this diverge?

```
length : NatList → Nat
length = λl.
  case unfold [NatList] l of
    inl _ => 0
  | inr p => succ (length l)
```

Spot and fix the bug.

---

## Code Review Exercises (30 minutes)

### Review 1: List Append ⭐⭐
Student's implementation:

```
append : NatList → NatList → NatList
append = λl1. λl2.
  case unfold [NatList] l1 of
    inl _ => l2
  | inr p => fold [NatList] (inr <fst p, append (snd p) l2>)
```

Review:
- Is this correct?
- Is this efficient?
- Any improvements?

### Review 2: Tree Height ⭐⭐
Two implementations:

**Version A**:
```
height = λt.
  case unfold [Tree] t of
    inl _ => 0
  | inr p => succ (max (height (fst p)) (height (snd p)))
```

**Version B**:
```
height = λt.
  case unfold [Tree] t of
    inl _ => 1
  | inr p => succ (max (height (fst p)) (height (snd p)))
```

Which is better and why?

### Review 3: Stream Generation ⭐⭐⭐
Student's code:

```
nats : Stream
nats = let helper = λn. fold [Stream] <n, helper (succ n)>
       in helper 0
```

Discuss:
- Does this work?
- What about termination?
- Alternative approaches?

---

## Theoretical Questions (30 minutes)

### Question 1: Fixed Points ⭐⭐
Explain the connection:

a) What is a fixed point of a function?
b) How is μα.T a fixed point?
c) Why is it the "least" fixed point?

### Question 2: Positive vs Negative ⭐⭐
Why do we care about occurrence positions?

a) What's a positive occurrence?
b) What's a negative occurrence?
c) Why are negative occurrences problematic?
d) Give an example of a negative occurrence

### Question 3: Termination ⭐⭐⭐
How do recursive types affect termination?

a) Does STLC terminate?
b) Does STLC + μ types terminate?
c) Give a non-terminating term
d) Can we recover termination?

---

## Solutions

### Warm-Up Solutions

**1.1**:
- a) `Unit + (μα. Unit + α)`
- b) `Nat × (μα. Nat × α)`
- c) `((μα. (α × α) + Nat) × (μα. (α × α) + Nat)) + Nat`

**1.2**:
- a) fold, b) fold, c) unfold, d) unfold

**1.3**:
- a) `Tree`
- b) `Nat + (Tree × Tree)`
- c) `Tree`

**1.4**:
- a) List of booleans
- b) List where each node has a Nat and two children (binary tree)
- c) Binary tree with Nat pairs at leaves

**1.5**:
- a) `Nat`
- b) `Nat × Stream`
- c) `zeros = fold [Stream] <0, zeros>`

### Standard Solutions

**2.1**:
```
a) append = λl1. λl2.
     case unfold [NatList] l1 of
       inl _ => l2
     | inr p => cons (fst p) (append (snd p) l2)

b) reverse = λl.
     case unfold [NatList] l of
       inl _ => nil
     | inr p => append (reverse (snd p)) (cons (fst p) nil)

c) map = λf. λl.
     case unfold [NatList] l of
       inl _ => nil
     | inr p => cons (f (fst p)) (map f (snd p))
```

**2.2**:
```
a) height = λt.
     case unfold [Tree] t of
       inl _ => 0
     | inr p => succ (max (height (fst p)) (height (snd p)))

b) mirror = λt.
     case unfold [Tree] t of
       inl n => leaf n
     | inr p => branch (mirror (snd p)) (mirror (fst p))

c) flatten = λt.
     case unfold [Tree] t of
       inl n => cons n nil
     | inr p => append (flatten (fst p))
                       (append (flatten (snd p)) nil)
```

**2.3**:
```
a) AltList = μα. Nat × (Unit + α)
b) single = λn. fold [AltList] <n, inl unit>
   cons = λn. λl. fold [AltList] <n, inr l>
c) toNatList walks the structure with unfold/case
```

**2.4**:
```
a) Either empty or (value, left subtree, right subtree)
b) insert uses unfold, compares, recursively inserts, folds
c) contains uses unfold, compares, recursively searches
```

**2.6**:
```
a) RoseTree = μα. Nat × (μβ. Unit + (α × β))
b) Constructors: node with value and children list
c) depth recursively computes max depth of children + 1
```

**2.8**:
```
a) drop = λn. λs. if iszero n then s else drop (pred n) (tail s)
b) zipWith = λf. λs1. λs2.
     fold [Stream] <f (head s1) (head s2),
                    zipWith f (tail s1) (tail s2)>
c) iterate = λf. λx. fold [Stream] <x, iterate f (f x)>
```

### Challenge Solutions

**3.1**:
```
Fix T = μα. (α → T) → T
fix : (T → T) → T
fix = λf. (λx. f (unfold x x)) (fold (λx. f (unfold x x)))

This creates non-termination: fix id → fix id → ...
```

**3.2**:
- Inductive: defined by constructors, finite
- Coinductive: defined by destructors, potentially infinite
- Fundamental: how we build vs how we observe
- Infinite lists: No with strict evaluation, yes with lazy

**3.3**:
- Pure μ can't express dependent types
- Need refinement types or dependent types
- Sized types track termination via size metrics

**3.4**:
- Church: `pred` is O(n), complex
- Scott: `pred` is O(1), simple
- Scott better for computation, Church better for polymorphism

**3.5**:
- Equality: `μα.T = T[μα.T/α]` always
- Need coinductive algorithm to check
- α-equivalence needed
- Much harder than syntactic equality

**3.6**:
- Can construct, but leads to logical inconsistency
- Enables typing of paradoxes
- Some systems allow for expressiveness
- Must be careful with logic interpretation

### Debug Solutions

**Debug 1**: Missing fold: `nil = fold [NatList] (inl unit)`

**Debug 2**: Missing unfold: `case unfold [NatList] l of`

**Debug 3**: Wrong annotation: Use `fold [NatList]` not unfolded type

**Debug 4**: Strict evaluation prevents self-reference. Need fixpoint combinator or lazy evaluation.

**Debug 5**: Wrong constructor. Should be `inr <leaf 1, leaf 2>` not pair.

**Debug 6**: Should recurse on `snd p`, not `l`: `succ (length (snd p))`

### Code Review Solutions

**Review 1**: Correct and reasonably efficient. Could eta-reduce.

**Review 2**: Depends on convention. A: empty = height 0, B: empty = height 1. Both valid, be consistent.

**Review 3**: Works in theory, requires general recursion. In practice, need fixpoint combinator or language support.

### Theoretical Solutions

**Question 1**:
- Fixed point f(x) = x
- μα.T satisfies T[μα.T/α] ≅ μα.T
- Least because it's the smallest such type

**Question 2**:
- Positive: right of even number of arrows
- Negative: right of odd number of arrows
- Negative allows paradoxes (like Russell's paradox)
- Example: `α → Nat` (α is negative)

**Question 3**:
- STLC terminates (strongly normalizing)
- STLC + μ doesn't terminate
- Non-terminating: `(λx. unfold x x) (fold (λx. unfold x x))`
- Can use sized types or guardedness

---

**Estimated Time**: 4-6 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 6 hard, 6 debug, 3 review, 3 theory

**Note**: These problems complement the main exercises. Focus on understanding the μ type mechanism!
