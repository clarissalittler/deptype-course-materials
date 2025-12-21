# Chapter 14: Row Types & Extensible Records - Exercises

## Exercise 1: Record Operations

Evaluate these expressions by hand:
1. `{x = 0, y = true}.x`
2. `{z = 1 | {x = 0, y = true}}.z`
3. `{x = 0, y = true} \ x`

## Exercise 2: Row Polymorphism

Write the type for a function that adds an "id" field to any record:
```
addId : ∀ρ. {| ρ} -> {id: Nat | ρ}
```

## Exercise 3: Variant Types

Define a type for optional values using variants:
```
Option a = <None: Unit | Some: a>
```

Write `none` and `some` constructors.

## Exercise 4: Polymorphic Variants

Explain the difference between:
1. `<A: Nat, B: Bool>`
2. `<A: Nat | ρ>`

## Exercise 5: Implement Record Update

Add a record update operation:
```
t.l := t'   -- Update field l with value t'
```

## Challenge: First-Class Labels

Extend the system with first-class labels that can be passed as arguments.

## References
- Leijen, "Extensible Records with Scoped Labels" (2005)
- Rémy, "Type Inference for Records" (1989)
