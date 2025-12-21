# Chapter 13: Gradual Typing - Exercises

## Exercise 1: Understanding Consistency

Determine if the following type pairs are consistent (T₁ ~ T₂):

1. `Nat ~ ?`
2. `? ~ Bool`
3. `Nat -> Bool ~ ? -> ?`
4. `Nat -> Bool ~ ? -> Nat`
5. `Nat -> Bool ~ Bool -> Nat`
6. `(? -> Nat) -> Bool ~ (Nat -> ?) -> ?`

## Exercise 2: Type Checking

What type does each expression have in gradual typing?

1. `λx : ?. x`
2. `λx : ?. succ x`
3. `(λx : ?. x) true`
4. `(λf : ?. f 0) (λx : Nat. x)`
5. `λf : ? -> Nat. λx : ?. f x`

## Exercise 3: Cast Insertion

Show the explicit casts inserted for each term:

1. `(λx : ?. x) 0`
2. `(λf : ? -> Nat. f true) (λx : ?. 0)`
3. `if (x : ?) then 0 else 1` (where x : ?)

## Exercise 4: Blame Tracking

For each expression, identify where blame would be assigned if a runtime error occurs:

1. `(λx : Nat. x) ((λy : ?. y) true)`
2. `(λf : Nat -> Nat. f true) (λx : ?. x)`
3. `let f = (λx : ?. succ x) in f true`

## Exercise 5: Ground Types

Explain why ground types are important in the cast semantics:

1. Why is `? -> ?` a ground type but `Nat -> Bool` is not?
2. How do casts decompose through ground types?
3. What happens when casting `Nat -> Bool` to `?`?

## Exercise 6: Meet and Join

Calculate the meet (⊓) and join (⊔) of these type pairs:

1. `Nat ⊓ ?`
2. `? ⊓ ?`
3. `(Nat -> Bool) ⊓ (? -> ?)`
4. `Nat ⊔ ?`
5. `(Nat -> ?) ⊔ (? -> Bool)`

## Exercise 7: Implement Positive/Negative Blame

Currently, all casts blame the same label. Implement positive/negative blame:

- Positive blame: Caller provided wrong value
- Negative blame: Function returned wrong value

```
<T₁ => T₂>^(p,n) t
```

Update:
1. `BlameLabel` to be `(String, String)`
2. Cast semantics to flip blame for contravariant positions
3. Tests

## Exercise 8: Add Product Types

Extend gradual typing with product types:

1. Add `T₁ × T₂` to the type syntax
2. Define consistency for products
3. Add pairs and projections to terms
4. Implement cast semantics for products

## Exercise 9: Gradual Guarantee

Prove (informally) that the gradual guarantee holds:

**Gradual Guarantee**: If `e` has type `T` and `e'` is obtained by making types in `e` more precise, then `e'` also has type `T'` where `T' ⊑ T`.

Consider these cases:
1. Replacing `?` with `Nat` in a function parameter
2. Replacing `?` with `Nat -> Bool` in a return type

## Exercise 10: Space-Efficient Casts

The naive cast calculus can lead to unbounded cast accumulation. Implement space-efficient casts using coercions:

```
c ::= ι           -- Identity
    | G!          -- Injection into ?
    | G?^l        -- Projection from ?
    | c₁ -> c₂    -- Function coercion
    | c₁; c₂      -- Composition
```

Key optimization: Compose adjacent casts into single coercions.

## Challenge Exercises

### Challenge 1: Gradual Rows

Extend gradual typing to records with gradual row types:

```
{l₁: T₁, l₂: T₂ | ρ}  -- Open record with row variable
{l: T | ?}            -- Gradual row
```

### Challenge 2: Gradual Parametricity

Explore gradual parametric polymorphism:

```
∀α. α -> α    vs    ? -> ?
```

What happens when a polymorphic function is cast to/from the dynamic type?

### Challenge 3: Gradual Type Inference

Implement type inference that infers the most precise types while leaving some positions as `?`:

```
infer :: Term -> (Type, Constraints)
solve :: Constraints -> Substitution
```

The result should be the principal gradual type.

### Challenge 4: Blame Theorems

Prove the blame theorem: "Well-typed programs can't be blamed."

More precisely: If a cast `<T₁ => T₂>^l v` fails with blame `l`, then either:
- The positive blame is justified (caller error)
- The negative blame is justified (callee error)

## References

- Siek & Taha, "Gradual Typing for Functional Languages" (2006)
- Wadler & Findler, "Well-Typed Programs Can't Be Blamed" (2009)
- Siek et al., "Refined Criteria for Gradual Typing" (2015)
- Garcia et al., "Abstracting Gradual Typing" (2016)
- Cimini & Siek, "The Gradualizer" (2016)
- New & Ahmed, "Graduality from Embedding-Projection Pairs" (2018)
