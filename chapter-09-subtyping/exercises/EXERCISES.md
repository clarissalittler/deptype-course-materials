# Chapter 9: Subtyping - Exercises

These exercises explore subtyping relations, variance, and their interaction with type checking.

## Exercise 1: Subtype Relationships

Determine whether the following subtype relationships hold. Justify your answer.

1. `{x: Nat, y: Bool, z: Top}` <: `{x: Nat, y: Bool}`
2. `{x: Nat}` <: `{x: Nat, y: Bool}`
3. `(Top -> Bool)` <: `(Nat -> Bool)`
4. `(Nat -> Bool)` <: `(Top -> Bool)`
5. `(Bool -> Bot)` <: `(Bool -> Nat)`
6. `{f: Nat -> Bool}` <: `{f: Top -> Bool}`
7. `{point: {x: Nat, y: Nat, z: Nat}}` <: `{point: {x: Nat, y: Nat}}`

**Hint**: Remember that functions are contravariant in their argument type and covariant in their result type.

## Exercise 2: Maximum and Minimum Types

For each of the following expressions, find:
- The **most specific** (smallest/minimum) type
- The **most general** (largest/maximum) type it can be ascribed to

```
1. λx:Nat. x
2. λx:Top. 0
3. {name = true, age = succ 0}
4. λr:{x: Nat}. r.x
```

## Exercise 3: Join and Meet

Compute the join (least upper bound) and meet (greatest lower bound) for these type pairs:

1. `{x: Nat, y: Bool}` and `{x: Nat, z: Top}`
2. `(Nat -> Bool)` and `(Bool -> Bool)`
3. `{a: Top}` and `{a: Bot}`
4. `(Top -> Bot)` and `(Bot -> Top)`

**Note**: The join is used for if-then-else branches. The meet is used when intersecting capabilities.

## Exercise 4: Subtyping Derivations

Write formal derivation trees for these subtyping judgments:

1. `{x: Bot, y: Bool} <: {x: Nat}`
2. `(Top -> {a: Nat, b: Bool}) <: (Bool -> {a: Nat})`
3. `{f: Top -> Bot} <: {f: Nat -> Bool}`

## Exercise 5: Implementing Bounded Quantification

Extend the type system with bounded polymorphism (F<:):

```
Type ::= ... | ∀α <: T. T'
Term ::= ... | Λα <: T. t | t [T]
```

Rules:
- `Γ, α <: T ⊢ t : T'` implies `Γ ⊢ Λα <: T. t : ∀α <: T. T'`
- If `Γ ⊢ t : ∀α <: T. T'` and `S <: T`, then `Γ ⊢ t [S] : [α ↦ S]T'`

Implement:
1. Extend `Syntax.hs` with bounded quantification
2. Extend `TypeCheck.hs` with bounded type application
3. Add test cases

## Exercise 6: Covariant and Contravariant Positions

For each occurrence of `X` in these types, determine if it's in a covariant (+), contravariant (-), or invariant (±) position:

1. `X -> Bool`
2. `Bool -> X`
3. `(X -> Bool) -> Nat`
4. `(Bool -> X) -> Nat`
5. `{field: X -> X}`
6. `(X -> X) -> (X -> X)`

**Hint**: Every arrow flips the variance of its left side.

## Exercise 7: Row Polymorphism

Implement row polymorphism as an alternative to record subtyping:

```
Type ::= ... | {l₁: T₁, ... | ρ}   -- record with row variable
```

A row variable `ρ` represents "the rest of the fields". This allows:
```
λr:{x: Nat | ρ}. r.x
```
to accept any record with at least an `x: Nat` field.

Implement:
1. Row variables in the type syntax
2. Row unification in type checking
3. Compare to width subtyping

## Exercise 8: Algorithmic Subtyping

The subtyping algorithm in the implementation is syntax-directed. Prove that:

1. The algorithm terminates (structural induction on types)
2. The algorithm is sound (if it returns True, then the subtyping holds)
3. The algorithm is complete (if subtyping holds, it returns True)

## Exercise 9: Least Upper Bound Computation

Prove that the `join` function computes the least upper bound:

1. For all T1, T2: T1 <: join(T1, T2) and T2 <: join(T1, T2)
2. For all T1, T2, U: if T1 <: U and T2 <: U, then join(T1, T2) <: U

**Hint**: Use structural induction on types.

## Exercise 10: Object-Oriented Encoding

Using records and subtyping, encode a simple object system:

1. Define a "Point" type with x, y coordinates
2. Define a "ColoredPoint" type that extends Point with a color field
3. Write a function that works on any Point (including ColoredPoints)
4. Demonstrate width subtyping in action

```haskell
-- Example:
point : {x: Nat, y: Nat}
coloredPoint : {x: Nat, y: Nat, color: Bool}

distance : {x: Nat, y: Nat} -> Nat
-- Should work on both point and coloredPoint
```

## Challenge Exercises

### Challenge 1: Intersection Types

Add intersection types `T1 ∧ T2`:

- A value of type `T1 ∧ T2` has both type `T1` and type `T2`
- Subtyping: `T1 ∧ T2 <: T1` and `T1 ∧ T2 <: T2`
- If `T <: T1` and `T <: T2`, then `T <: T1 ∧ T2`

### Challenge 2: Union Types

Add union types `T1 ∨ T2`:

- A value of type `T1 ∨ T2` is either of type `T1` or type `T2`
- Subtyping: `T1 <: T1 ∨ T2` and `T2 <: T1 ∨ T2`
- Elimination requires case analysis

### Challenge 3: Self Types

Implement self types for encoding recursive object types:

```
Self(X). {method: X -> X}
```

This allows methods to return the "same type as the receiver".

## References

- Pierce, "Types and Programming Languages", Chapters 15-16 (Subtyping)
- Cardelli, "A Semantics of Multiple Inheritance" (1988)
- Cardelli & Wegner, "On Understanding Types, Data Abstraction, and Polymorphism" (1985)
- Pierce & Turner, "Local Type Inference" (2000)
