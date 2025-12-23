# Chapter 14: Row Types & Extensible Records - Tutorial

This tutorial walks through row types with step-by-step examples.

## Part 1: The Record Problem

### Nominal Records

Most languages have "closed" record types:

```
type Point2D = {x: Nat, y: Nat}
type Point3D = {x: Nat, y: Nat, z: Nat}
```

Now consider a distance function:

```
distance : Point2D -> Nat
distance p = sqrt (p.x * p.x + p.y * p.y)
```

Can we call `distance` on a `Point3D`?

```
distance {x = 3, y = 4, z = 5}  -- ERROR!
```

No! Even though Point3D has all the fields Point2D needs.

### The Solution: Row Polymorphism

With row types:

```
distance : ∀ρ. {x: Nat, y: Nat | ρ} -> Nat
distance p = sqrt (p.x * p.x + p.y * p.y)
```

Now it works with ANY record having at least x and y:

```
distance {x = 3, y = 4}                 -- OK: ρ = ()
distance {x = 3, y = 4, z = 5}          -- OK: ρ = (z: Nat)
distance {x = 0, y = 1, color = "red"}  -- OK: ρ = (color: String)
```

## Part 2: Row Type Syntax

### Basic Rows

A row is a sequence of label-type pairs:

```
()                    -- Empty row
(x: Nat | ())         -- Single field x: Nat
(x: Nat | (y: Bool | ()))  -- Two fields
```

Shorthand: `(x: Nat, y: Bool)` means `(x: Nat | (y: Bool | ()))`.

### Row Variables

A row variable represents unknown fields:

```
ρ                     -- Unknown row
(x: Nat | ρ)          -- At least x, plus whatever ρ has
```

### Record Types from Rows

A record type wraps a row in braces:

```
{}                    -- Empty record
{x: Nat}              -- Record with just x
{x: Nat, y: Bool}     -- Record with x and y
{x: Nat | ρ}          -- Open record (at least x)
```

### Closed vs Open Records

**Closed** (all fields known):
```
{x: Nat, y: Bool}     -- Exactly x and y, nothing else
```

**Open** (some fields unknown):
```
{x: Nat | ρ}          -- x plus whatever ρ is
```

## Part 3: Record Operations

### Projection (Field Access)

Access a field with dot notation:

```
r.l

{x = 3, y = 4}.x      -- Result: 3
{name = "Alice"}.name -- Result: "Alice"
```

Typing:
```
   r : {l: T | ρ}
  ────────────────
     r.l : T
```

### Extension (Adding Fields)

Add a field with extension syntax:

```
{l = t | r}

{z = 5 | {x = 3, y = 4}}  -- Result: {x = 3, y = 4, z = 5}
```

**Important**: The label must NOT already exist in r!

Typing:
```
   r : {ρ}    t : T    l ∉ ρ
  ─────────────────────────────
    {l = t | r} : {l: T | ρ}
```

### Restriction (Removing Fields)

Remove a field with backslash:

```
r \ l

{x = 3, y = 4} \ x    -- Result: {y = 4}
{a = 1, b = 2, c = 3} \ b  -- Result: {a = 1, c = 3}
```

Typing:
```
   r : {l: T | ρ}
  ─────────────────
    r \ l : {ρ}
```

### Field Update

Update a field using restriction + extension:

```
update : ∀ρ. String -> {name: String | ρ} -> {name: String | ρ}
update newName r = {name = newName | r \ name}
```

Step by step:
1. `r \ name` removes the old name field
2. `{name = newName | ...}` adds the new one

## Part 4: Row Polymorphism

### Basic Pattern

Abstract over unknown fields:

```
getName : ∀ρ. {name: String | ρ} -> String
getName r = r.name
```

The `∀ρ` says "for any row ρ."

### Multiple Required Fields

Require several fields:

```
fullName : ∀ρ. {first: String, last: String | ρ} -> String
fullName r = r.first ++ " " ++ r.last
```

### Preserving Unknown Fields

Return a record with extra fields:

```
addId : ∀ρ. Nat -> {ρ} -> {id: Nat | ρ}
addId n r = {id = n | r}
```

Usage:
```
addId 42 {name = "Alice"}
-- Result: {id = 42, name = "Alice"}

addId 1 {x = 0, y = 0}
-- Result: {id = 1, x = 0, y = 0}
```

### Explicit Instantiation

Sometimes you need to specify the row:

```
identity : ∀ρ. {x: Nat | ρ} -> {x: Nat | ρ}
identity r = r

-- Explicit instantiation
identity [(y: Bool)] {x = 0, y = true}
```

## Part 5: Polymorphic Variants

### Closed Variants

Standard sum types are closed:

```
type Result = Ok Nat | Error String

handle : Result -> Nat
handle (Ok n) = n
handle (Error _) = 0
```

### Open Variants

Polymorphic variants are open:

```
<ok: Nat | ρ>     -- At least ok, maybe more
```

### Injection

Create a variant value:

```
<ok = 42>         -- Has type <ok: Nat | ρ>
<error = "fail">  -- Has type <error: String | ρ>
```

### Case Analysis

Handle variants:

```
handleResult : ∀ρ. <ok: Nat | error: String | ρ> -> Nat
handleResult v = case v of
  <ok = n> -> n
  <error = _> -> 0
  <other = _> -> 0   -- Handles remaining cases
```

### Open Handler

Handle some cases, leave others:

```
handleOk : ∀ρ. <ok: Nat | ρ> -> <done: Nat | ρ>
handleOk v = case v of
  <ok = n> -> <done = n>
  <other = x> -> <other = x>  -- Pass through
```

## Part 6: Row Unification

### Labels Can Reorder

Row types with same fields are equal:

```
{x: Nat, y: Bool} = {y: Bool, x: Nat}
```

Order doesn't matter!

### Unification with Variables

When unifying rows:

```
{x: Nat | α} ~ {x: Nat, y: Bool}
-- Solves: α = (y: Bool)

{x: Nat | α} ~ {y: Bool | β}
-- Solves: α = (y: Bool | γ), β = (x: Nat | γ)
```

### Lack Constraints

Ensure a label is absent:

```
addField : ∀ρ. (x ∉ ρ) => Nat -> {ρ} -> {x: Nat | ρ}
```

The constraint `x ∉ ρ` prevents duplicates.

## Practice Problems

### Problem 1: Write a Row-Polymorphic Function

Write a function that gets the age from any record with an age field:

```
getAge : ???
getAge r = r.age
```

<details>
<summary>Solution</summary>

```
getAge : ∀ρ. {age: Nat | ρ} -> Nat
getAge r = r.age
```
</details>

### Problem 2: Field Update

Write a function to increment the count field:

```
incCount : ∀ρ. {count: Nat | ρ} -> {count: Nat | ρ}
incCount = ???
```

<details>
<summary>Solution</summary>

```
incCount r = {count = r.count + 1 | r \ count}
```

Or equivalently:
```
incCount r = let c = r.count in {count = c + 1 | r \ count}
```
</details>

### Problem 3: Add Multiple Fields

Write a function that adds both x and y fields:

```
addCoords : ∀ρ. Nat -> Nat -> {ρ} -> {x: Nat, y: Nat | ρ}
addCoords x y r = ???
```

<details>
<summary>Solution</summary>

```
addCoords x y r = {x = x | {y = y | r}}
```

Or with explicit constraint:
```
addCoords : ∀ρ. (x ∉ ρ, y ∉ ρ) => Nat -> Nat -> {ρ} -> {x: Nat, y: Nat | ρ}
addCoords xv yv r = {x = xv | {y = yv | r}}
```
</details>

### Problem 4: Variant Handler

Write a handler that converts `<int: Nat>` to `<nat: Nat>`:

```
renameInt : ∀ρ. <int: Nat | ρ> -> <nat: Nat | ρ>
renameInt = ???
```

<details>
<summary>Solution</summary>

```
renameInt v = case v of
  <int = n> -> <nat = n>
  <other = x> -> <other = x>
```
</details>

### Problem 5: Why Doesn't This Work?

```
bad : ∀ρ. {x: Nat | ρ} -> {x: Bool | ρ}
bad r = {x = true | r}
```

<details>
<summary>Solution</summary>

Two problems:
1. `r` already has `x`, so extension would duplicate
2. We'd need: `{x = true | r \ x}` to remove first
3. But then return type has `x: Bool` with SAME `ρ`, which still contains original `x`!

Correct version:
```
replaceX : ∀ρ. {x: Nat | ρ} -> {x: Bool | ρ}
replaceX r = {x = true | r \ x}
```

Wait, this still doesn't work because `ρ` might contain `x: Nat`!

Actually, the original type is problematic. The `ρ` in input includes everything except `x: Nat`. The `ρ` in output should be the same. After removing `x` from input, we have `{ρ}`. Adding `x: Bool` gives `{x: Bool | ρ}`. This works if `x ∉ ρ` (which is implied by the input type structure).
</details>
