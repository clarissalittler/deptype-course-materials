# Chapter 15: Recursive Types (μ Types) - Common Mistakes

This guide covers frequent errors when learning recursive types.

---

## Mistake 1: Forgetting to Fold

### The Problem
Creating a recursive type value without fold.

### Wrong Code
```
nil : NatList
nil = inl unit    -- ERROR! Type is Unit + (Nat × NatList), not NatList
```

### Correct Code
```
nil : NatList
nil = fold [NatList] (inl unit)
```

### Why?
`fold` wraps the unfolded representation into the recursive type.

### How to Remember
> "Always fold to create, unfold to examine."

---

## Mistake 2: Forgetting to Unfold

### The Problem
Pattern matching on a recursive type without unfolding.

### Wrong Code
```
isEmpty : NatList → Bool
isEmpty = λl:NatList.
  case l of            -- ERROR! l has type NatList, not sum type
    inl _ => true
  | inr _ => false
```

### Correct Code
```
isEmpty = λl:NatList.
  case unfold [NatList] l of    -- Now it's Unit + (Nat × NatList)
    inl _ => true
  | inr _ => false
```

### Why?
The recursive type μα.T is NOT the same as T[μα.T/α]. Must unfold!

### How to Remember
> "Unfold before you can see inside."

---

## Mistake 3: Wrong Type Annotation in fold

### The Problem
Using wrong type in fold annotation.

### Wrong Code
```
nil = fold [Unit + (Nat × NatList)] (inl unit)
-- ERROR! Should annotate with the μ type, not the unfolded type
```

### Correct Code
```
nil = fold [μα. Unit + (Nat × α)] (inl unit)
-- Or with type alias:
nil = fold [NatList] (inl unit)
```

### Why?
fold takes the μ type as its annotation, not the body.

### How to Remember
> "fold [μ...] not fold [body...]"

---

## Mistake 4: Confusing Iso and Equi Semantics

### The Problem
Expecting types to be equal when they're only isomorphic.

### Wrong Thinking
```
NatList = Unit + (Nat × NatList)    -- WRONG in iso-recursive!
```

### Correct Understanding
```
NatList ≅ Unit + (Nat × NatList)    -- Isomorphic
NatList ≠ Unit + (Nat × NatList)    -- Not equal!
```

Must use fold/unfold to convert.

### How to Remember
> "Iso-recursive: similar but not same. Use fold/unfold."

---

## Mistake 5: Infinite Loops in Definitions

### The Problem
Writing definitions that don't terminate.

### Dangerous Code
```
ones = fold [Stream] <1, ones>
```

This requires the language to support general recursion! In a strict language without special support, this won't work.

### Safe Alternative
```
ones = fix (λself. fold [Stream] <1, self>)
-- Using a fixed-point combinator
```

### How to Remember
> "Infinite structures need general recursion support."

---

## Mistake 6: Missing Type Annotations

### The Problem
Omitting required type annotations on fold/unfold.

### Wrong Code
```
nil = fold (inl unit)    -- What recursive type?
```

### Correct Code
```
nil = fold [NatList] (inl unit)
```

### Why?
Fold and unfold need to know which μ type to use.

### How to Remember
> "fold and unfold always need [type] annotation."

---

## Mistake 7: Substitution Confusion

### The Problem
Not understanding what T[μα.T/α] means.

### The Pattern
`T[μα.T/α]` = "replace every α in T with the full μα.T"

### Example
```
T = Unit + (Nat × α)
μα.T = μα. Unit + (Nat × α)

T[μα.T/α] = Unit + (Nat × (μα. Unit + (Nat × α)))
                            ^^^^^^^^^^^^^^^^^^^^
                            α replaced with full μ type
```

### How to Remember
> "Substitution replaces the variable with the whole μ type."

---

## Mistake 8: Non-Positive Occurrences

### The Problem
Creating ill-formed recursive types with negative occurrences.

### Problematic Type
```
Bad = μα. α → Nat    -- α appears in negative (contravariant) position
```

This can lead to logical paradoxes in some systems!

### Usually OK Types
```
List = μα. Unit + (Nat × α)    -- α appears only positively
Tree = μα. Nat + (α × α)       -- α appears only positively
```

### How to Remember
> "Keep α in positive (right of arrows, in products) positions."

---

## Mistake 9: Confusing μ with Other Binders

### The Problem
Treating μ like λ or ∀.

### μ is NOT like λ
```
μα. T    -- Type-level fixed point, α is a TYPE variable
λx. t    -- Term-level function, x is a TERM variable
```

### μ is NOT like ∀
```
μα. T    -- α refers to the type itself (self-reference)
∀α. T    -- α is universally quantified (polymorphism)
```

### How to Remember
> "μ is for self-reference, not abstraction."

---

## Mistake 10: Expecting Direct Pattern Matching

### The Problem
Trying to match on constructors directly.

### Wrong Expectation
```
-- Like Haskell:
case l of
  Nil => ...
  Cons x xs => ...
```

### Reality
```
-- In raw μ types:
case unfold [NatList] l of
  inl _ => ...
  inr p => let x = fst p in let xs = snd p in ...
```

### Why?
μ types use sums and products, not named constructors.

### How to Remember
> "μ types are low-level. unfold to sums, destruct products."

---

## Debugging Checklist

When recursive type checking fails:

1. **Check fold**: Did you wrap with fold [μ...] ?
2. **Check unfold**: Did you unwrap before case analysis?
3. **Check annotation**: Is the type annotation correct?
4. **Check substitution**: Does the inner type match after substitution?
5. **Check positivity**: Is α in positive positions only?

---

## Practice Problems

### Problem 1: Find the Error

```
head : NatList → Nat
head = λl:NatList.
  case l of
    inl _ => 0
  | inr p => fst p
```

<details>
<summary>Answer</summary>

Missing unfold!

```
head = λl:NatList.
  case unfold [NatList] l of
    inl _ => 0
  | inr p => fst p
```
</details>

### Problem 2: Fix the Type

```
cons : Nat → NatList → NatList
cons = λn:Nat. λl:NatList. inr <n, l>
```

<details>
<summary>Answer</summary>

Missing fold!

```
cons = λn:Nat. λl:NatList.
  fold [NatList] (inr <n, l>)
```
</details>

### Problem 3: What's Wrong?

```
Tree = μα. Nat + α + α
```

<details>
<summary>Answer</summary>

This represents: "either a Nat, or a Tree, or a Tree"
But the structure is unusual. Normally for binary trees:

```
Tree = μα. Nat + (α × α)
```

The original isn't wrong per se, but it's a strange tree where a branch has only ONE child (either left or right), not two.
</details>
