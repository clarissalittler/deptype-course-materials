# Chapter 15: Recursive Types - Exercises

## Overview

These exercises explore recursive types (μ types), which allow us to define types
that refer to themselves. This is essential for representing data structures like
lists, trees, and streams in typed lambda calculi.

---

## Exercise 1: Understanding μ Types (Conceptual)

### 1.1 Type Unfolding

Given the recursive type for natural number lists:
```
NatList = μα. Unit + (Nat × α)
```

**Question:** What is the result of unfolding this type once? Explain what each
component represents.

**Hint:** Unfolding replaces α with the whole μ type.

### 1.2 Iso-recursive vs Equi-recursive

Explain the difference between:
- **Iso-recursive types:** μα.T is isomorphic to (but distinct from) T[μα.T/α]
- **Equi-recursive types:** μα.T is definitionally equal to T[μα.T/α]

**Question:** Why might a language implementer choose iso-recursive semantics?
What are the trade-offs?

### 1.3 Type Equivalence

Consider these two types:
```
T1 = μα. Nat → α
T2 = μβ. Nat → β
```

**Question:** Should these types be considered equal? What about:
```
T3 = μα. Nat → (Nat → α)
```
Is T3 equal to T1 or T2?

---

## Exercise 2: Encoding Data Structures

### 2.1 Binary Trees

Define a recursive type for binary trees with natural number leaves:
```
Tree = μα. Nat + (α × α)
```

**Task:** Implement the following in our calculus:
1. `leaf : Nat → Tree` - Create a leaf node
2. `node : Tree → Tree → Tree` - Create an internal node
3. `sumTree : Tree → Nat` - Sum all values in a tree

**Starter code:**
```
-- Leaf constructor
let leaf = λn:Nat. fold [Tree] (inl n as Nat + (Tree × Tree)) in

-- Node constructor
let node = λl:Tree. λr:Tree. fold [Tree] (inr <l, r> as Nat + (Tree × Tree)) in

-- Sum function (exercise: complete this)
let sumTree = λt:Tree.
  case unfold [Tree] t of
    inl n => ???
  | inr p => ???
in
```

### 2.2 Streams (Infinite Lists)

A stream is an infinite sequence of values:
```
Stream = μα. Nat × α
```

**Task:** Implement:
1. `constStream : Nat → Stream` - Infinite stream of a constant
2. `head : Stream → Nat` - Get the first element
3. `tail : Stream → Stream` - Get the rest of the stream

**Question:** Can we define a stream of ascending natural numbers? Why or why not?

### 2.3 Optional Values

Define the Option type:
```
Option A = μα. Unit + A
```

Wait—this doesn't actually need recursion!

**Question:** When is recursion necessary in a type definition vs when can we
use regular sum types?

---

## Exercise 3: The Lambda Calculus in Lambda Calculus

### 3.1 Untyped Terms

We can encode untyped lambda calculus terms as a recursive type:
```
UTerm = μα. Nat + (α × α) + α
       -- Var n | App t1 t2 | Lam body
```

**Task:** Encode the following untyped terms:
1. The identity function: λx. x
2. The self-application ω: λx. x x
3. The diverging term Ω: (λx. x x)(λx. x x)

**Note:** Variables are represented by de Bruijn indices (natural numbers).

### 3.2 Typed Self-Application

In simply typed lambda calculus, we cannot type `λx. x x`. But with recursive types:

```
SelfApp = μα. α → Nat
```

**Task:** Implement a well-typed version of `λx. x x` that produces a natural number.

**Hint:**
```
let omega = λx:SelfApp. (unfold [SelfApp] x) x in
fold [SelfApp] omega
```

Verify this type-checks and explain how fold/unfold break the "occurs check."

---

## Exercise 4: Fixed Points and Recursion

### 4.1 General Recursion from μ Types

The Y combinator provides general recursion. With recursive types, we can type it!

```
Fix A = μα. α → A
```

**Task:** Implement a typed fixed-point combinator:
```
fix : (A → A) → A
```

**Starter:**
```
let fix = λf:(Nat → Nat).
  let g = λx:Fix. f ((unfold [Fix] x) x) in
  g (fold [Fix] g)
in
```

Test it by implementing factorial.

### 4.2 Non-termination

**Question:** The typed lambda calculus (without recursive types) is strongly
normalizing—all programs terminate. With μ types, we can write non-terminating
programs. Give an example and explain why this happens.

---

## Exercise 5: Type System Extensions

### 5.1 Positive and Negative Occurrences

A type variable α occurs **positively** in T if it appears in an even number of
left-hand sides of arrows. It occurs **negatively** if odd.

For example, in `(α → Nat) → α`:
- The first α (in `α → Nat`) occurs negatively (once on the left)
- The second α occurs positively (zero times on the left)

**Question:** Why do some type systems require μα.T to only bind positive
occurrences of α? Consider:
```
Bad = μα. α → α
```

### 5.2 Least vs Greatest Fixed Points

In category theory, μα.T is the **least fixed point** (initial algebra), while
να.T is the **greatest fixed point** (final coalgebra).

- Least fixed points correspond to **inductive** data (finite, well-founded)
- Greatest fixed points correspond to **coinductive** data (possibly infinite)

**Task:** Explain why:
- `List = μα. 1 + (Nat × α)` contains only finite lists
- `Stream = να. Nat × α` can contain infinite streams

What would happen if we used ν for lists or μ for streams?

---

## Exercise 6: Implementation Challenges

### 6.1 Type Equality

With recursive types, type equality becomes more complex. Consider:
```
T1 = μα. Nat × (Nat × α)
T2 = μβ. Nat × β
```

**Question:** Are these types equal? How would you implement a type equality
checker for equi-recursive types?

**Hint:** Research "regular trees" and how type equality reduces to language
equivalence of finite automata.

### 6.2 Recursive Type Inference

**Question:** Can we infer recursive types, or must they be explicitly annotated?
Consider:
```
let f = λx. x x in f
```

What type should this have? Discuss the challenges of inferring μ types.

---

## Challenge Problems

### Challenge 1: Church-Encoded Lists with Types

Typically, Church encodings don't need recursive types:
```
List A = ∀R. (A → R → R) → R → R
```

**Task:** Compare this encoding with:
```
List A = μα. Unit + (A × α)
```

When would you prefer each encoding?

### Challenge 2: Nested Recursion

Define a type for "bushes"—trees where each node has a list of children:
```
Bush = μα. Nat × List α
```

But List is itself defined using μ! Write out the fully expanded type and
implement:
1. A leaf constructor
2. A multi-child node constructor
3. A function to count all leaves

### Challenge 3: Mutual Recursion

How would you encode mutually recursive types? For example, trees and forests:
```
Tree = Nat × Forest
Forest = List Tree
```

**Hint:** You can encode mutual recursion using products in a single μ type.

---

## Solutions Approach

For each exercise:

1. **Type first:** Write down the types of all components
2. **Use fold/unfold:** Every recursive type operation needs explicit fold or unfold
3. **Test incrementally:** Build complex terms from simpler, tested pieces
4. **Trace evaluation:** For understanding, manually trace fold/unfold operations

Remember:
- `fold [μα.T] e` introduces a value of the recursive type
- `unfold [μα.T] e` eliminates it, exposing the structure
- These are inverses: `unfold (fold v) = v`
