# Chapter 14: Row Types & Extensible Records - Cheat Sheet

## Core Concept

**Row polymorphism** allows functions to work with records having "at least" certain fields, enabling structural typing with full type inference.

## Row Syntax

```
ρ ::= ()                    Empty row
    | (l: T | ρ)            Row extension (field l:T, rest ρ)
    | α                     Row variable (unknown fields)
```

## Type Syntax

```
T ::= Bool | Nat | Unit     Base types
    | T₁ -> T₂              Function type
    | {ρ}                   Record type
    | <ρ>                   Variant type
    | ∀α. T                 Row polymorphism
```

## Term Syntax

```
t ::= {l₁=t₁, l₂=t₂, ...}   Record literal
    | t.l                   Projection (field access)
    | {l=t | r}             Record extension (add field)
    | r \ l                 Record restriction (remove field)
    | <l=t> : T             Variant injection
    | case t of ...         Case analysis
    | Λα. t                 Row abstraction
    | t [ρ]                 Row application
```

## Record Types

### Closed Records
```
{x: Nat, y: Bool}           Exactly these fields
{name: String}              Just name field
{}                          Empty record
```

### Open Records
```
{x: Nat | ρ}                At least x, plus row ρ
{x: Nat, y: Bool | ρ}       At least x and y
∀ρ. {name: String | ρ}      Row-polymorphic
```

## Key Type Rules

### Projection
```
   Γ ⊢ r : {l: T | ρ}
  ────────────────────
     Γ ⊢ r.l : T
```

Access field `l` from record with at least that field.

### Extension
```
   Γ ⊢ r : {ρ}    Γ ⊢ t : T    l ∉ ρ
  ──────────────────────────────────
    Γ ⊢ {l = t | r} : {l: T | ρ}
```

Add field `l` to record (must not already exist).

### Restriction
```
   Γ ⊢ r : {l: T | ρ}
  ─────────────────────
     Γ ⊢ r \ l : {ρ}
```

Remove field `l` from record.

### Row Polymorphism
```
      Γ ⊢ t : T    α ∉ FV(Γ)
  ────────────────────────────
      Γ ⊢ Λα. t : ∀α. T
```

Abstract over row variable `α`.

## Row Polymorphic Functions

### Basic Pattern
```
getName : ∀ρ. {name: String | ρ} -> String
getName r = r.name
```

Works with ANY record containing `name` field.

### Multiple Fields
```
fullName : ∀ρ. {first: String, last: String | ρ} -> String
fullName r = r.first ++ " " ++ r.last
```

### Preserving Fields
```
addAge : ∀ρ. Nat -> {ρ} -> {age: Nat | ρ}
addAge n r = {age = n | r}
```

Input has row `ρ`, output adds `age` field.

### Field Update
```
updateName : ∀ρ. String -> {name: String | ρ} -> {name: String | ρ}
updateName newName r = {name = newName | r \ name}
```

Remove old `name`, add new one.

## Record Operations

### Projection (Access)
```
{x = 3, y = 4}.x            →  3
{name = "Alice"}.name       →  "Alice"
```

### Extension (Add)
```
{z = 5 | {x = 3, y = 4}}    →  {x = 3, y = 4, z = 5}
{age = 30 | {name = "Bob"}} →  {name = "Bob", age = 30}
```

### Restriction (Remove)
```
{x = 3, y = 4} \ x          →  {y = 4}
{a = 1, b = 2, c = 3} \ b   →  {a = 1, c = 3}
```

### Update Pattern
```
{name = "Carol" | {name = "Bob", age = 30} \ name}
→ {name = "Carol", age = 30}
```

## Row Unification

### Labels Can Reorder
```
{x: Nat, y: Bool} = {y: Bool, x: Nat}
```

Order doesn't matter!

### Unifying with Variables
```
{x: Nat | α} ~ {x: Nat, y: Bool}
Solves: α = (y: Bool | ())

{x: Nat | α} ~ {y: Bool | β}
Solves: α = (y: Bool | γ), β = (x: Nat | γ)
```

### Lack Constraints
```
(l ∉ ρ)                     Label l not in row ρ
```

Ensures no duplicate fields when extending.

## Polymorphic Variants

### Variant Types
```
<ok: Nat | ρ>               At least ok case
<error: String | ρ>         At least error case
<int: Nat | float: Nat | ρ> At least int and float
```

### Injection
```
<ok = 42> : <ok: Nat | ρ>
<error = "fail"> : <error: String | ρ>
```

### Case Analysis
```
handleResult : ∀ρ. <ok: Nat | error: String | ρ> -> Nat
handleResult v = case v of
  <ok = n> -> n
  <error = _> -> 0
  <other = _> -> 0
```

### Open Handler
```
mapOk : ∀ρ. (Nat -> Nat) -> <ok: Nat | ρ> -> <ok: Nat | ρ>
mapOk f v = case v of
  <ok = n> -> <ok = f n>
  <other = x> -> <other = x>
```

## Common Patterns

### Get Field (Row-Polymorphic)
```
getX : ∀ρ. {x: Nat | ρ} -> Nat
getX r = r.x
```

### Set Field (Row-Polymorphic)
```
setX : ∀ρ. Nat -> {x: Nat | ρ} -> {x: Nat | ρ}
setX n r = {x = n | r \ x}
```

### Add Field
```
addField : ∀ρ. (l ∉ ρ) => T -> {ρ} -> {l: T | ρ}
addField v r = {l = v | r}
```

### Remove Field
```
removeField : ∀ρ. {l: T | ρ} -> {ρ}
removeField r = r \ l
```

### Extend Multiple Fields
```
addCoords : ∀ρ. Nat -> Nat -> {ρ} -> {x: Nat, y: Nat | ρ}
addCoords x y r = {x = x | {y = y | r}}
```

### Record Merge (if no overlap)
```
merge : ∀ρ₁ ρ₂. {ρ₁} -> {ρ₂} -> {ρ₁, ρ₂}
```

Requires `ρ₁` and `ρ₂` are disjoint (no common labels).

## Duality: Records ↔ Variants

| Records | Variants |
|---------|----------|
| {l: T | ρ} | <l: T | ρ> |
| Projection r.l | Injection <l=t> |
| "Has all of" (∧) | "Is one of" (∨) |
| Extension {l=t | r} | Case analysis |
| At least these fields | At least these cases |

## Type Precision

Row types have precision ordering:

```
{x: Nat} ⊑ {x: Nat | ρ}        More specific ⊑ more general
{x: Nat, y: Bool} ⊑ {x: Nat | ρ}
() ⊑ ρ                          Empty ⊑ any row
```

More fields = more precise!

## Evaluation Rules

### Projection
```
{..., l = v, ...}.l  →  v
```

### Extension
```
{l = v | {l₁ = v₁, ..., lₙ = vₙ}}
→ {l = v, l₁ = v₁, ..., lₙ = vₙ}
```

### Restriction
```
{l₁ = v₁, ..., l = v, ..., lₙ = vₙ} \ l
→ {l₁ = v₁, ..., lₙ = vₙ}
```

### Case Analysis
```
case <l = v> of
  <l = x> -> t₁
  ...
→ [x ↦ v]t₁
```

## Row Operations (Implementation)

### Check if label in row
```haskell
rowHas :: Label -> Row -> Bool
rowHas l RowEmpty = False
rowHas l (RowExtend l' _ rest)
  | l == l' = True
  | otherwise = rowHas l rest
rowHas l (RowVar _) = False  -- Unknown
```

### Get type of label in row
```haskell
rowGet :: Label -> Row -> Maybe Type
rowGet l (RowExtend l' ty rest)
  | l == l' = Just ty
  | otherwise = rowGet l rest
rowGet _ _ = Nothing
```

### Extend row
```haskell
rowExtend :: Label -> Type -> Row -> Row
rowExtend = RowExtend
```

## Connection to Subtyping

Row polymorphism provides similar expressiveness to **width subtyping**:

| Subtyping | Row Polymorphism |
|-----------|------------------|
| {x: Nat, y: Bool} <: {x: Nat} | {x: Nat | ρ} with ρ = (y: Bool) |
| Subsumption | Instantiation |
| Limited inference | Full inference |

Row polymorphism has **better inference** properties!

## Real Languages

| Language | Feature | Syntax Example |
|----------|---------|----------------|
| **PureScript** | Full row polymorphism | `type Point r = {x :: Number, y :: Number | r}` |
| **Elm** | Extensible records | `{r | x : Int}` |
| **OCaml** | Polymorphic variants | `` `Ok 42 `` |
| **TypeScript** | Structural typing | `{x: number, ...}` (no row vars) |
| **Koka** | Effect rows | `{exn, div | e}` |

## Common Mistakes

### Mistake 1: Duplicate Extension
```
{x = 5 | {x = 3, y = 4}}    ✗ WRONG! x already exists
```

Must remove first:
```
{x = 5 | {x = 3, y = 4} \ x}  ✓ CORRECT
```

### Mistake 2: Assuming Closed
```
f : {x: Nat} -> Nat         -- Closed: ONLY x
f r = r.y                   -- ERROR: y doesn't exist
```

Need:
```
f : {x: Nat, y: Nat | ρ} -> Nat
```

### Mistake 3: Order Dependence
```
{x: Nat, y: Bool} ≠ {y: Bool, x: Nat}  ✗ WRONG!
```

They ARE equal (order doesn't matter):
```
{x: Nat, y: Bool} = {y: Bool, x: Nat}  ✓ CORRECT
```

### Mistake 4: Forgetting Lack Constraint
```
add : ∀ρ. T -> {ρ} -> {l: T | ρ}    -- Might add duplicate!
```

Should be:
```
add : ∀ρ. (l ∉ ρ) => T -> {ρ} -> {l: T | ρ}
```

## Quick Reference Examples

### 2D Point (Extensible)
```
type Point2D ρ = {x: Nat, y: Nat | ρ}

magnitude : ∀ρ. Point2D ρ -> Nat
magnitude p = sqrt (p.x * p.x + p.y * p.y)

-- Works with:
magnitude {x = 3, y = 4}                 ✓
magnitude {x = 0, y = 1, z = 2}          ✓
magnitude {x = 1, y = 2, color = "red"}  ✓
```

### Person Record (Extensible)
```
type Person ρ = {name: String, age: Nat | ρ}

greet : ∀ρ. Person ρ -> String
greet p = "Hello, " ++ p.name

-- Works with:
greet {name = "Alice", age = 30}                      ✓
greet {name = "Bob", age = 25, job = "Engineer"}      ✓
```

### Result Variant (Extensible)
```
type Result α ρ = <ok: α | error: String | ρ>

mapResult : ∀α β ρ. (α -> β) -> Result α ρ -> Result β ρ
mapResult f v = case v of
  <ok = x> -> <ok = f x>
  <error = e> -> <error = e>
  <other = x> -> <other = x>
```

## Debugging Tips

### 1. Check Row Variables
Are row variables properly quantified?
```
∀ρ. {x: Nat | ρ} -> Nat     ✓ Quantified
{x: Nat | ρ} -> Nat          ✗ Free variable ρ
```

### 2. Trace Unification
When unification fails, check:
- Are labels consistent?
- Do row variables unify correctly?
- Is there a lack constraint violation?

### 3. Verify Lack Constraints
When extending, ensure:
```
{l = t | r}  -- l must NOT be in r
```

### 4. Use Explicit Instantiation
If inference fails, instantiate explicitly:
```
f [(y: Bool | ())] {x = 0, y = true}
```

## Further Reading

### Foundational Papers

- **Wand (1987)**: Row polymorphism for objects
- **Rémy (1989)**: Row polymorphism for ML records
- **Cardelli & Mitchell (1991)**: Operations on records
- **Leijen (2005)**: Extensible records with scoped labels
- **Hillerström & Lindley (2016)**: Row types for effects

## Next Steps

- **Effect systems**: Row types for effect tracking
- **Object encoding**: Use rows to model objects
- **Gradual rows**: Combine with gradual typing
- **Scoped labels**: Handle duplicate labels
