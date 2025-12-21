# Chapter 9: Subtyping - Frequently Asked Questions

## Conceptual Questions

### Q: What is subtyping and why do we need it?

**A:** Subtyping is a relationship between types that allows a value of one type to be used where another type is expected. We write `S <: T` to mean "S is a subtype of T" (or equivalently, "T is a supertype of S").

Subtyping adds flexibility to type systems. Without it, if a function expects a `{x: Nat, y: Nat}` record, you can't pass a `{x: Nat, y: Nat, color: Bool}` record, even though it has all the required fields. With subtyping, this works because having more fields makes a record "more specific."

Real-world example: In OOP languages, you can pass a `ColoredPoint` to a function expecting a `Point` because `ColoredPoint` extends `Point`.

### Q: What's the difference between Top and Bot?

**A:**
- **Top** is the supertype of every type. Every value can be "viewed as" a Top. It's like saying "this is a thing" without being more specific.
- **Bot** is the subtype of every type. There are no values of type Bot (in a sound system). It represents "no possible value" or "divergence."

Think of it as:
- Top: "I don't know what type this is, but it's something"
- Bot: "This will never produce a value" (e.g., infinite loop, exception)

### Q: Why are functions contravariant in their argument?

**A:** This is often confusing at first! Consider:

```
If we have f : Animal -> String
We want to use it where g : Dog -> String is expected
```

This seems backwards - why would a function on *more general* input be usable where *more specific* input is expected?

The key insight: **Callers provide the argument.** If code expects `g : Dog -> String`, callers will pass Dogs. If we substitute `f : Animal -> String`, f can handle Dogs because Dogs are Animals. The function can accept *at least* what's needed.

Conversely, if we have `h : Dog -> String` and try to use it where `Animal -> String` is expected, callers might pass Cats, and `h` can't handle that!

### Q: What does "width subtyping" mean for records?

**A:** Width subtyping means records with *more* fields are subtypes of records with *fewer* fields:

```
{x: Nat, y: Nat, z: Nat} <: {x: Nat, y: Nat} <: {x: Nat}
```

This seems backwards until you think about it: a record with more fields can be used anywhere a record with fewer fields is needed - you just ignore the extra fields.

### Q: What's depth subtyping for records?

**A:** Depth subtyping means if each field's type is a subtype, the whole record is a subtype:

```
{name: Bot} <: {name: String}   -- if Bot <: String
```

Combined with width subtyping, you get:
```
{x: Bot, y: Nat, z: Bool} <: {x: Nat, y: Top}
-- width: drop z
-- depth: Bot <: Nat, Nat <: Top
```

### Q: What is the Liskov Substitution Principle?

**A:** The LSP states: "If S is a subtype of T, then objects of type T may be replaced with objects of type S without altering any of the desirable properties of the program."

In other words, subtypes must be *behaviorally compatible* with their supertypes. If code works with T, it should work with any S <: T.

This is why function contravariance/covariance matters - it ensures behavioral substitutability.

## Implementation Questions

### Q: How is subtyping checked algorithmically?

**A:** The algorithm is syntax-directed:

1. If types are equal, return True (reflexivity)
2. If supertype is Top, return True
3. If subtype is Bot, return True
4. For functions: check contravariant arg, covariant result
5. For records: check all supertype fields exist in subtype with subtype relations

```haskell
subtype t1 t2
  | t1 == t2 = True
  | TyTop <- t2 = True
  | TyBot <- t1 = True
  | TyArr s1 s2 <- t1, TyArr u1 u2 <- t2
    = subtype u1 s1 && subtype s2 u2
  | TyRecord f1 <- t1, TyRecord f2 <- t2
    = all (fieldOk f1) (Map.toList f2)
  | otherwise = False
```

### Q: What is subsumption and how is it used in type checking?

**A:** Subsumption is the typing rule that allows implicit upcasting:

```
Γ ⊢ t : S    S <: T
─────────────────── (T-Sub)
     Γ ⊢ t : T
```

In the implementation, we apply subsumption at specific points:
- Function application: argument type must be subtype of parameter type
- Ascription: term type must be subtype of annotated type
- If-then-else: we compute the join of branch types

### Q: What are join and meet?

**A:**
- **Join** (⊔): Least upper bound. `A ⊔ B` is the smallest type that's a supertype of both A and B.
- **Meet** (⊓): Greatest lower bound. `A ⊓ B` is the largest type that's a subtype of both A and B.

Uses:
- Join: Computing result type of if-then-else branches
- Meet: Computing intersection of requirements (e.g., function argument in join)

Example:
```
{x: Nat, y: Bool} ⊔ {x: Nat, z: Top} = {x: Nat}  -- common fields only
{x: Nat} ⊓ {y: Bool} = {x: Nat, y: Bool}         -- all fields
```

### Q: Why does type ascription exist?

**A:** Ascription (`t as T`) has several purposes:

1. **Explicit upcast**: Tell the type checker to use a more general type
2. **Documentation**: Make the intended type clear in code
3. **Control inference**: In systems with inference, force a specific type

Example:
```
-- Without ascription, this has type {x: Nat, y: Bool}
{x = 0, y = true}

-- With ascription, we get type {x: Nat}
({x = 0, y = true} as {x: Nat})
```

## Common Confusions

### Q: Why can't I use Bool where Top is expected if Bool <: Top?

**A:** You *can*! That's exactly what subtyping allows. If `f : Top -> Nat`, then `f true` type checks because `true : Bool` and `Bool <: Top`.

### Q: Why doesn't `{x: Nat} <: {x: Nat, y: Bool}` hold?

**A:** Width subtyping goes the other way! The record with *more* fields is the subtype:
```
{x: Nat, y: Bool} <: {x: Nat}   -- OK
{x: Nat} <: {x: Nat, y: Bool}   -- WRONG
```

Think about it: if you need a record with x and y, you can't use a record that only has x.

### Q: Are mutable references covariant or contravariant?

**A:** Neither - they're **invariant**! A mutable reference is both read (covariant) and written (contravariant), so it must be invariant.

If `Ref[Dog] <: Ref[Animal]`, you could:
1. Write a Cat to the Ref[Animal]
2. Read it back as a Dog from the Ref[Dog]
3. Call a Dog-specific method on a Cat

This is why Java arrays (which are mutable and covariant) are unsound and require runtime checks.

### Q: What's the difference between subtyping and polymorphism?

**A:**
- **Subtyping** (this chapter): S <: T means any S value can be used as a T
- **Polymorphism** (Chapter 5): `∀α. τ` means works for any type α

Key differences:
- Subtyping allows implicit coercion between types
- Polymorphism treats types uniformly (parametrically)
- You can combine them (bounded polymorphism: `∀α <: T. ...`)

### Q: Why do we need both Top and polymorphism?

**A:** They serve different purposes:

```
-- With Top (subtyping):
f : Top -> Top
-- f can receive any value, but loses type information
-- f(0) : Top, not Nat

-- With polymorphism:
g : ∀α. α -> α
-- g preserves type: g[Nat](0) : Nat
```

Top is the "I don't care" type; polymorphism is "I care, but uniformly."

## Troubleshooting

### Q: My subtype check is failing unexpectedly. What should I check?

**A:** Common issues:
1. **Wrong direction**: Remember `{more fields} <: {fewer fields}`
2. **Contravariance**: For functions, argument subtyping is reversed
3. **Missing fields**: In record subtyping, supertype's fields must all exist in subtype
4. **Base type mismatch**: `Bool <: Nat` doesn't hold (only Bot <: Nat <: Top)

### Q: Why isn't my ascription working?

**A:** Ascription only allows *upcasting*, not *downcasting*:
```
true as Top     -- OK: Bool <: Top
true as Nat     -- FAILS: Bool is not a subtype of Nat
```

You can't cast to a more specific type, only a more general one.

### Q: The join of my branch types isn't what I expected.

**A:** Remember how join works:
- For records: only *common* fields are kept
- For functions: argument types are *met*, result types are joined
- If no good join exists, Top is returned

```
{x: Nat, y: Bool} ⊔ {x: Nat, z: Top}
= {x: Nat}  -- Only x is common
```
