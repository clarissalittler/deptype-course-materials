# Chapter 3: STLC with Algebraic Data Types - Frequently Asked Questions

## Table of Contents

1. [Conceptual Questions](#conceptual-questions)
2. [Product Types](#product-types)
3. [Sum Types](#sum-types)
4. [Records and Variants](#records-and-variants)
5. [Pattern Matching](#pattern-matching)
6. [Lists](#lists)
7. [Practical "I'm Stuck" Scenarios](#practical-im-stuck-scenarios)

---

## Conceptual Questions

### Q1: What are "algebraic" data types?

**A**: Types built from two operations:
- **Products** (AND): `A × B` contains A AND B
- **Sums** (OR): `A + B` contains A OR B

They're "algebraic" because they follow algebra-like laws:
```
A × 1 ≅ A        (unit is identity for product)
A + 0 ≅ A        (empty is identity for sum)
A × (B + C) ≅ (A × B) + (A × C)  (distributive law)
```

### Q2: Why add ADTs to STLC?

**A**: ADTs let us represent **real data**:
- Pairs: coordinates, key-value pairs
- Options: nullable values without null
- Lists: sequences of data
- Trees: hierarchical structures

Without ADTs, STLC can only compute with base types!

### Q3: How do ADTs relate to types in real languages?

**A**:

| Concept | Haskell | Rust | TypeScript |
|---------|---------|------|------------|
| Product | `(a, b)` | `(A, B)` | `[A, B]` |
| Sum | `Either a b` | `Result<A, B>` | `A \| B` |
| Record | `data R = R {x::Int}` | `struct` | `{x: number}` |
| Variant | `data V = A \| B` | `enum` | discriminated union |

### Q4: What's the difference between products and sums?

**A**:

**Product** `A × B`: Contains BOTH an A AND a B
```
pair : A × B
fst pair : A
snd pair : B
```

**Sum** `A + B`: Contains EITHER an A OR a B
```
left a  : A + B  (contains A)
right b : A + B  (contains B)
```

---

## Product Types

### Q5: What is a product type?

**A**: A type containing multiple values:
```
Point = Nat × Nat
origin : Point = (0, 0)

fst origin = 0
snd origin = 0
```

The number of values of type `A × B` = (values of A) × (values of B).

### Q6: How do I create and use pairs?

**A**:
```
-- Create
pair = (3, true) : Nat × Bool

-- Access
fst pair : Nat  = 3
snd pair : Bool = true
```

### Q7: Can I have nested products?

**A**: Yes! Products can contain products:
```
((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)
```

But consider records for clarity when nesting gets deep.

### Q8: What's the unit type?

**A**: The product of zero things! Written `Unit` or `()`:
```
Unit : Type
() : Unit
```

Only ONE value of type Unit - it carries no information.

Uses:
- Return type for side-effecting functions (if we had them)
- Placeholder in generic code

---

## Sum Types

### Q9: What is a sum type?

**A**: A type representing a choice:
```
MaybeNat = Unit + Nat

none : MaybeNat = inl ()      -- "nothing"
some5 : MaybeNat = inr 5      -- "just 5"
```

The number of values of type `A + B` = (values of A) + (values of B).

### Q10: How do I create sum values?

**A**: Use injection:
```
inl : A → A + B     -- inject left
inr : B → A + B     -- inject right
```

The type annotation on `inl` tells us what B is:
```
inl [Nat + Bool] 5   : Nat + Bool
inr [Nat + Bool] true : Nat + Bool
```

### Q11: How do I use sum values?

**A**: Case analysis:
```
case x of
  inl a => handle_a(a)
  inr b => handle_b(b)
```

You MUST handle both cases - the type checker enforces this!

### Q12: What's the empty type?

**A**: The sum of zero things! Written `Empty` or `Void`:
```
Empty : Type
-- NO values of type Empty!
```

If you have `x : Empty`, you can prove anything (ex falso quodlibet).

---

## Records and Variants

### Q13: How are records different from products?

**A**: Records have **named** fields:
```
-- Product (position-based)
(5, "Alice") : Nat × String

-- Record (name-based)
{age = 5, name = "Alice"} : {age: Nat, name: String}
```

Records are clearer for complex data.

### Q14: How do I access record fields?

**A**: By name:
```
person = {age = 30, name = "Bob"}

person.age  : Nat    = 30
person.name : String = "Bob"
```

### Q15: What are variants?

**A**: Named sum types:
```
Shape = <circle: Nat, rect: Nat × Nat>

myCircle = <circle = 5> as Shape   -- circle with radius 5
myRect = <rect = (3, 4)> as Shape  -- 3×4 rectangle
```

Match on the tag name:
```
case shape of
  <circle = r> => pi * r * r
  <rect = (w, h)> => w * h
```

---

## Pattern Matching

### Q16: What is pattern matching?

**A**: Destructuring data by its shape:
```
case list of
  [] => 0
  (x :: xs) => 1 + length xs
```

Patterns can be nested:
```
case pair of
  ((a, b), (c, d)) => a + b + c + d
```

### Q17: What makes a pattern set "exhaustive"?

**A**: Every possible value is covered:
```
-- Exhaustive:
case bool of
  true => ...
  false => ...

-- NOT exhaustive:
case maybeNat of
  inr n => ...    -- Missing inl case!
```

The type checker warns about non-exhaustive patterns.

### Q18: Can patterns overlap?

**A**: Yes, first match wins:
```
case n of
  0 => "zero"
  _ => "nonzero"   -- Catch-all
```

**Warning**: Put specific patterns first, catch-alls last!

### Q19: What are the different pattern forms?

**A**:
- **Variable**: `x` - matches anything, binds to x
- **Wildcard**: `_` - matches anything, no binding
- **Constructor**: `inl x`, `(a, b)`, etc.
- **Literal**: `0`, `true`, etc.
- **Nested**: `(inl (x, y))`

---

## Lists

### Q20: How are lists represented?

**A**: Recursive sum type:
```
List A = Unit + (A × List A)
       = Nil  + Cons
```

Syntax sugar:
```
[]        = inl ()           -- empty list
x :: xs   = inr (x, xs)      -- cons
[1,2,3]   = 1 :: 2 :: 3 :: []
```

### Q21: How do I write list functions?

**A**: Pattern match on empty vs non-empty:
```
length : List A → Nat
length list = case list of
  [] => 0
  (x :: xs) => 1 + length xs
```

### Q22: What's the type of map?

**A**:
```
map : (A → B) → List A → List B
map f list = case list of
  [] => []
  (x :: xs) => f x :: map f xs
```

### Q23: How do I handle "nullable" values?

**A**: Use option type instead of null:
```
Option A = Unit + A
none : Option A = inl ()
some : A → Option A = λx. inr x
```

Pattern match to handle both cases - no null pointer exceptions!

---

## Practical "I'm Stuck" Scenarios

### Q24: "Type mismatch in case branches"

**A**: All branches must return the same type:
```
-- Wrong:
case x of
  inl a => 5        -- Nat
  inr b => true     -- Bool  ← Type mismatch!

-- Right:
case x of
  inl a => 5        -- Nat
  inr b => 0        -- Nat  ✓
```

### Q25: "Cannot infer injection type"

**A**: Sum types need annotation:
```
-- Wrong:
inl 5       -- What's the right component?

-- Right:
inl 5 as Nat + Bool
```

### Q26: "Non-exhaustive pattern match"

**A**: Cover all cases:
```
-- Warning: missing false case
case b of
  true => 1

-- Fixed:
case b of
  true => 1
  false => 0
```

### Q27: "How do I update a record field?"

**A**: Create a new record with the changed field:
```
updateAge : {age: Nat, name: String} → Nat → {age: Nat, name: String}
updateAge person newAge = {age = newAge, name = person.name}
```

(We don't have mutation - this is pure functional programming!)

### Q28: "My recursive function doesn't terminate"

**A**: Check that you:
1. Have a base case (`[]`, `0`, `none`, etc.)
2. Recurse on smaller data
3. Handle all patterns

### Q29: "How do I combine Option and List?"

**A**: They compose nicely:
```
-- Find first element satisfying predicate
find : (A → Bool) → List A → Option A
find p list = case list of
  [] => none
  (x :: xs) => if p x then some x else find p xs
```

---

## Quick Reference: Typing Rules

**Products**:
```
Γ ⊢ t₁ : A    Γ ⊢ t₂ : B
─────────────────────────── (T-Pair)
Γ ⊢ (t₁, t₂) : A × B

Γ ⊢ t : A × B               Γ ⊢ t : A × B
───────────── (T-Fst)       ───────────── (T-Snd)
Γ ⊢ fst t : A               Γ ⊢ snd t : B
```

**Sums**:
```
Γ ⊢ t : A                   Γ ⊢ t : B
───────────────── (T-Inl)   ───────────────── (T-Inr)
Γ ⊢ inl t : A + B           Γ ⊢ inr t : A + B

Γ ⊢ t : A + B    Γ,x:A ⊢ t₁ : C    Γ,y:B ⊢ t₂ : C
─────────────────────────────────────────────────── (T-Case)
Γ ⊢ case t of inl x => t₁ | inr y => t₂ : C
```

---

## Further Reading

- **Pierce TAPL Chapters 11**: Products and sums
- **Harper PFPL Chapter 14**: Sum types
- **Wadler (1987)**: "Views" paper on pattern matching

**Remember**: ADTs give you the building blocks for all data structures. Master products and sums, and you can build anything!
