# Chapter 14: Row Types & Extensible Records - Common Mistakes

This guide covers frequent errors when learning row types.

---

## Mistake 1: Confusing Closed and Open Records

### The Problem
Thinking `{x: Nat}` and `{x: Nat | ρ}` are the same.

### The Difference
```
{x: Nat}      -- Closed: EXACTLY x and nothing else
{x: Nat | ρ}  -- Open: AT LEAST x, possibly more fields
```

### Example
```
f : {x: Nat} -> Nat
f r = r.x

f {x = 1, y = 2}  -- ERROR! y is extra

g : ∀ρ. {x: Nat | ρ} -> Nat
g r = r.x

g {x = 1, y = 2}  -- OK! Extra fields allowed
```

### How to Remember
> "No ρ = exactly those fields. With ρ = at least those fields."

---

## Mistake 2: Extending with Duplicate Field

### The Problem
Trying to add a field that already exists.

### Wrong Code
```
{x = 5 | {x = 3, y = 4}}  -- ERROR! x already exists
```

### Correct Code
```
-- First remove, then add
{x = 5 | {x = 3, y = 4} \ x}  -- OK: {x = 5, y = 4}
```

### Why?
Record extension creates a NEW field. If it exists, you'd have duplicates.

### How to Remember
> "Extension adds. Use restriction first to update."

---

## Mistake 3: Thinking Order Matters

### The Problem
Assuming `{x: Nat, y: Bool}` ≠ `{y: Bool, x: Nat}`.

### Correct Understanding
Row types are UNORDERED:
```
{x: Nat, y: Bool} = {y: Bool, x: Nat}
```

The type checker treats them as equal.

### Why?
Rows are like sets/maps of labels, not sequences.

### How to Remember
> "Rows are sets of labels. Order doesn't matter."

---

## Mistake 4: Forgetting the Row Variable in Return Type

### The Problem
Losing extra fields in function output.

### Wrong Code
```
getX : ∀ρ. {x: Nat | ρ} -> {x: Nat}  -- Returns closed record!
getX r = r
```

If you pass `{x = 1, y = 2}`, you lose y!

### Correct Code
```
getX : ∀ρ. {x: Nat | ρ} -> {x: Nat | ρ}  -- Preserves ρ
getX r = r
```

### How to Remember
> "If you want to preserve fields, keep ρ in return type."

---

## Mistake 5: Accessing Unknown Fields

### The Problem
Trying to access fields in the unknown part ρ.

### Wrong Code
```
getY : ∀ρ. {x: Nat | ρ} -> Nat
getY r = r.y  -- ERROR! y might not be in ρ
```

### Correct Code
```
getY : ∀ρ. {x: Nat, y: Nat | ρ} -> Nat
getY r = r.y  -- OK: y is explicitly required
```

### How to Remember
> "You can only access fields you explicitly require."

---

## Mistake 6: Confusing Type-Level and Term-Level

### The Problem
Mixing row syntax between types and terms.

### Type Level (Row)
```
{x: Nat | ρ}        -- ρ is a ROW variable
(x: Nat | ρ)        -- Row with x, rest is ρ
```

### Term Level (Record)
```
{x = 5 | r}         -- r is a RECORD value
{x = 5, y = true}   -- Record literal
```

### How to Remember
> "Types use : for fields. Terms use = for values."

---

## Mistake 7: Expecting Subtyping Behavior

### The Problem
Thinking row polymorphism IS subtyping.

### Row Polymorphism
```
f : ∀ρ. {x: Nat | ρ} -> Nat
-- f accepts records with at least x
```

### Subtyping
```
{x: Nat, y: Bool} <: {x: Nat}
-- Bigger record is subtype of smaller
```

### Key Difference
- Row polymorphism: Universal quantification (∀)
- Subtyping: Subtype relation (<:)

Row polymorphism has BETTER type inference!

### How to Remember
> "Row polymorphism uses ∀, not <:. Better inference."

---

## Mistake 8: Variant vs Record Confusion

### The Problem
Treating variants like records.

### Records (Product)
```
{x: Nat, y: Bool}   -- Has BOTH x AND y
```

### Variants (Sum)
```
<x: Nat | y: Bool>  -- Has EITHER x OR y
```

### Accessing
```
r.x           -- Record: always works if x is there
case v of ... -- Variant: must match all cases
```

### How to Remember
> "Records are AND (all fields). Variants are OR (one case)."

---

## Mistake 9: Missing Lack Constraints

### The Problem
Not preventing duplicate fields in extensions.

### Without Constraint
```
addX : ∀ρ. {ρ} -> {x: Nat | ρ}
addX r = {x = 0 | r}

addX {x = 5}  -- What happens? Duplicate x!
```

### With Lack Constraint
```
addX : ∀ρ. (x ∉ ρ) => {ρ} -> {x: Nat | ρ}
addX r = {x = 0 | r}

addX {x = 5}  -- TYPE ERROR: x is in ρ, violates constraint
```

### How to Remember
> "Use lack constraints (l ∉ ρ) to prevent duplicates."

---

## Mistake 10: Wrong Variant Pattern

### The Problem
Not handling remaining cases in open variants.

### Wrong Code
```
handle : ∀ρ. <ok: Nat | error: String | ρ> -> Nat
handle v = case v of
  <ok = n> -> n
  <error = _> -> 0
  -- Missing: what about cases in ρ?
```

### Correct Code
```
handle v = case v of
  <ok = n> -> n
  <error = _> -> 0
  <other = _> -> 0  -- Catch-all for unknown cases
```

### How to Remember
> "Open variants need catch-all patterns for ρ."

---

## Debugging Checklist

When row type checking fails:

1. **Open vs closed**: Did you include ρ where needed?
2. **Duplicate fields**: Are you extending with existing field?
3. **Unknown access**: Are you accessing a field not in the required row?
4. **Preserve ρ**: Does return type keep the row variable?
5. **Variant patterns**: Did you handle all cases?

---

## Practice Problems

### Problem 1: Find the Error

```
swap : {x: Nat, y: Nat} -> {x: Nat, y: Nat}
swap r = {x = r.y, y = r.x}
```

What's limiting about this type?

<details>
<summary>Answer</summary>

It's closed! Can't use with records having extra fields.

Better:
```
swap : ∀ρ. {x: Nat, y: Nat | ρ} -> {x: Nat, y: Nat | ρ}
swap r = {x = r.y | {y = r.x | r \ x \ y}}
```
</details>

### Problem 2: Fix This

```
addName : String -> {ρ} -> {name: String | ρ}
addName n r = {name = n | r}
```

What if r already has name?

<details>
<summary>Answer</summary>

Need lack constraint:
```
addName : ∀ρ. (name ∉ ρ) => String -> {ρ} -> {name: String | ρ}
```

Or handle update case:
```
setName : ∀ρ. String -> {name: String | ρ} -> {name: String | ρ}
setName n r = {name = n | r \ name}
```
</details>

### Problem 3: Why Wrong?

```
getFirst : ∀ρ. <first: Nat | ρ> -> Nat
getFirst v = case v of
  <first = n> -> n
```

<details>
<summary>Answer</summary>

Missing handler for ρ cases! What if v is some other case?

Fix:
```
getFirst v = case v of
  <first = n> -> n
  <other = _> -> 0  -- Or handle appropriately
```
</details>
