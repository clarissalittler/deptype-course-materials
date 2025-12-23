# Chapter 14: Row Types & Extensible Records - REPL User Guide

## Overview

The Row Types REPL provides an interactive environment for experimenting with row polymorphism, extensible records, polymorphic variants, and structural typing.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-14-row-types
stack build

# Run the REPL
stack exec row-repl
```

### Quick Start

```
row> {x = 3, y = 4}
  {x = 3, y = 4}

row> :type {x = 3, y = 4}
  {x: Nat, y: Nat}

row> λr. r.x
  λr. r.x

row> :type λr. r.x
  ∀ρ. {x: α | ρ} -> α
```

## Features

### 1. Record Creation and Access

Create records with field literals:

```
row> {name = "Alice", age = 30}
  {name = "Alice", age = 30}

row> :type {x = 0, y = true}
  {x: Nat, y: Bool}

row> {x = 3, y = 4, z = 5}.y
  4
```

### 2. Row-Polymorphic Functions

Write functions that work with any compatible record:

```
row> :let getName = λr. r.name
  getName : ∀ρ. {name: String | ρ} -> String

row> getName {name = "Alice"}
  "Alice"

row> getName {name = "Bob", age = 30}
  "Bob"

row> getName {name = "Carol", age = 25, email = "c@e.com"}
  "Carol"
```

### 3. Record Extension

Add fields to records:

```
row> {z = 5 | {x = 3, y = 4}}
  {x = 3, y = 4, z = 5}

row> :let addAge = λn. λr. {age = n | r}
  addAge : ∀ρ. Nat -> {ρ} -> {age: Nat | ρ}

row> addAge 30 {name = "Alice"}
  {name = "Alice", age = 30}
```

### 4. Record Restriction

Remove fields from records:

```
row> {x = 3, y = 4, z = 5} \ y
  {x = 3, z = 5}

row> :let removeAge = λr. r \ age
  removeAge : ∀ρ. {age: T | ρ} -> {ρ}

row> removeAge {name = "Alice", age = 30}
  {name = "Alice"}
```

### 5. Field Update

Combine restriction and extension:

```
row> :let setName = λname. λr. {name = name | r \ name}
  setName : ∀ρ. String -> {name: String | ρ} -> {name: String | ρ}

row> setName "Carol" {name = "Alice", age = 30}
  {name = "Carol", age = 30}

row> :let incAge = λr. {age = r.age + 1 | r \ age}
  incAge : ∀ρ. {age: Nat | ρ} -> {age: Nat | ρ}

row> incAge {name = "Bob", age = 29}
  {name = "Bob", age = 30}
```

### 6. Row Type Inspection

Examine row types:

```
row> :expand {x: Nat, y: Bool}
  {(x: Nat | (y: Bool | ()))}

row> :expand ∀ρ. {x: Nat | ρ}
  ∀ρ. {(x: Nat | ρ)}

row> :rowvars ∀ρ₁ ρ₂. {x: Nat | ρ₁} -> {y: Bool | ρ₂}
  Row variables: ρ₁, ρ₂
```

### 7. Polymorphic Variants

Create and handle open sum types:

```
row> <ok = 42>
  <ok = 42>

row> :type <ok = 42>
  <ok: Nat | ρ>

row> :let handleOk = λv. case v of
       <ok = n> -> n
       <other = _> -> 0
  handleOk : ∀ρ. <ok: Nat | ρ> -> Nat

row> handleOk (<ok = 42> : <ok: Nat | error: String | ρ>)
  42

row> handleOk (<error = "fail"> : <ok: Nat | error: String | ρ>)
  0
```

### 8. Lack Constraints

Verify that labels don't exist:

```
row> :lacks x (y: Bool, z: Nat)
  true

row> :lacks x (x: Nat, y: Bool)
  false

row> :type λr. {x = 0 | r}
  ∀ρ. (x ∉ ρ) => {ρ} -> {x: Nat | ρ}
```

## Command Reference

### Type Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:type <term>` | `:t` | Show type of term |
| `:expand <type>` | `:e` | Expand row type to show structure |
| `:rowvars <type>` | `:rv` | Show row variables in type |
| `:lacks <label> <row>` | `:l` | Check if label absent from row |

### Row Operations

| Command | Short | Description |
|---------|-------|-------------|
| `:project <record> <label>` | `:p` | Access field |
| `:extend <label> <value> <record>` | `:ext` | Add field |
| `:restrict <record> <label>` | `:res` | Remove field |
| `:update <label> <value> <record>` | `:upd` | Update field |

### Evaluation Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:eval <term>` | `:e` | Evaluate term completely |
| `:step` | | Enable step-by-step mode |
| `:nostep` | | Disable step-by-step mode |
| `:trace` | | Show reduction steps |
| `:notrace` | | Hide reduction steps |

### Binding Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:let name = term` | | Define a binding |
| `:bindings` | `:b` | Show all bindings |
| `:clear` | | Clear all bindings |

### Information Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:help` | `:h`, `:?` | Show help message |
| `:examples` | `:ex` | Show example terms |
| `:quit` | `:q`, `:exit` | Exit the REPL |

## Practical Examples

### Example 1: 2D and 3D Points

```
row> :let magnitude2d = λp. sqrt (p.x * p.x + p.y * p.y)
  magnitude2d : ∀ρ. {x: Nat, y: Nat | ρ} -> Nat

row> magnitude2d {x = 3, y = 4}
  5

row> magnitude2d {x = 3, y = 4, z = 5}
  5

row> magnitude2d {x = 0, y = 1, color = "red", label = "origin"}
  1
```

The same function works with 2D points, 3D points, and decorated points!

### Example 2: Person Records

```
row> :let greet = λp. "Hello, " ++ p.name
  greet : ∀ρ. {name: String | ρ} -> String

row> :let age_next_year = λp. p.age + 1
  age_next_year : ∀ρ. {age: Nat | ρ} -> Nat

row> greet {name = "Alice", age = 30}
  "Hello, Alice"

row> age_next_year {name = "Bob", age = 25, email = "bob@example.com"}
  26
```

### Example 3: Building Records Incrementally

```
row> :let empty = {}
  empty : {}

row> :let withName = {name = "Alice" | empty}
  withName : {name: String}

row> :let withAge = {age = 30 | withName}
  withAge : {name: String, age: Nat}

row> :let withEmail = {email = "alice@example.com" | withAge}
  withEmail : {name: String, age: Nat, email: String}
```

### Example 4: Record Update Pattern

```
row> :let person = {name = "Alice", age = 30, email = "alice@e.com"}

row> :let updateName = λnewName. λr. {name = newName | r \ name}

row> updateName "Alicia" person
  {name = "Alicia", age = 30, email = "alice@e.com"}

row> :let celebrateBirthday = λr. {age = r.age + 1 | r \ age}

row> celebrateBirthday person
  {name = "Alice", age = 31, email = "alice@e.com"}
```

### Example 5: Polymorphic Variants

```
row> :let ok = λx. <ok = x>
  ok : ∀α ρ. α -> <ok: α | ρ>

row> :let error = λmsg. <error = msg>
  error : ∀ρ. String -> <error: String | ρ>

row> :let unwrap = λdef. λv. case v of
       <ok = x> -> x
       <error = _> -> def
       <other = _> -> def
  unwrap : ∀α ρ. α -> <ok: α | error: String | ρ> -> α

row> unwrap 0 (ok 42)
  42

row> unwrap 0 (error "failed")
  0
```

### Example 6: Compositional Extensions

```
row> :let addId = λn. λr. {id = n | r}
  addId : ∀ρ. Nat -> {ρ} -> {id: Nat | ρ}

row> :let addTimestamp = λt. λr. {timestamp = t | r}
  addTimestamp : ∀ρ. Nat -> {ρ} -> {timestamp: Nat | ρ}

row> :let base = {name = "Alice"}

row> addId 1 base
  {id = 1, name = "Alice"}

row> addTimestamp 1234567890 (addId 1 base)
  {id = 1, name = "Alice", timestamp = 1234567890}
```

## Advanced Features

### Row Unification

See how row types unify:

```
row> :unify {x: Nat | α} {x: Nat, y: Bool}
  Solution: α = (y: Bool | ())

row> :unify {x: Nat | α} {y: Bool | β}
  Solution: α = (y: Bool | γ), β = (x: Nat | γ) where γ is fresh

row> :unify {x: Nat, y: Bool} {y: Bool, x: Nat}
  Solution: already equal (order doesn't matter)
```

### Lack Constraint Checking

```
row> :let safeAdd = λl. λv. λr.
       if (lacks l r)
       then {l = v | r}
       else r
  safeAdd : ∀ρ. Label -> α -> {ρ} -> {ρ} | {l: α | ρ}

row> safeAdd 'x 5 {y = 10}
  {x = 5, y = 10}

row> safeAdd 'x 5 {x = 3, y = 10}
  {x = 3, y = 10}  -- x already exists, unchanged
```

### Row Reordering

```
row> {x = 3, y = 4} : {x: Nat, y: Bool}
  TYPE ERROR: Nat ≠ Bool

row> {x = 3, y = 4} : {y: Nat, x: Nat}
  {x = 3, y = 4}  -- Order doesn't matter in types!

row> :type {x = 3, y = 4}
  {x: Nat, y: Nat}

row> :type {y = 4, x = 3}
  {x: Nat, y: Nat}  -- Same type!
```

### Multiple Row Variables

```
row> :type λr1. λr2. {x = r1.x, y = r2.y}
  ∀ρ₁ ρ₂. {x: α | ρ₁} -> {y: β | ρ₂} -> {x: α, y: β}

row> :let combine = λr1. λr2. {x = r1.x, y = r2.y}

row> combine {x = 3, a = 1} {y = 4, b = 2}
  {x = 3, y = 4}
```

## Common Patterns

### Pattern 1: Getter

```
row> :let getField = λl. λr. r.l
  getField : ∀ρ α. {l: α | ρ} -> α
```

### Pattern 2: Setter

```
row> :let setField = λl. λv. λr. {l = v | r \ l}
  setField : ∀ρ α. α -> {l: α | ρ} -> {l: α | ρ}
```

### Pattern 3: Projection

```
row> :let projectXY = λr. {x = r.x, y = r.y}
  projectXY : ∀ρ. {x: α, y: β | ρ} -> {x: α, y: β}
```

### Pattern 4: Merge (Disjoint)

```
row> :let merge = λr1. λr2. {??? | r1}
  -- Hard to implement! Needs structural induction
```

### Pattern 5: Rename Field

```
row> :let rename = λold. λnew. λr. {new = r.old | r \ old}
  rename : ∀ρ α. {old: α | ρ} -> {new: α | ρ}
```

## Exercises in the REPL

### Exercise 1: Basic Operations

Try these:
```
row> {x = 1, y = 2}.x
row> {z = 3 | {x = 1, y = 2}}
row> {x = 1, y = 2, z = 3} \ y
```

### Exercise 2: Row-Polymorphic Functions

Define and test:
```
row> :let fullName = λr. r.first ++ " " ++ r.last
row> fullName {first = "Alice", last = "Smith"}
row> fullName {first = "Bob", last = "Jones", age = 30}
```

### Exercise 3: Field Update

Implement:
```
row> :let doubleAge = λr. {age = r.age * 2 | r \ age}
row> doubleAge {name = "Alice", age = 15}
```

### Exercise 4: Multiple Fields

Access multiple fields:
```
row> :let distance = λp1. λp2.
       sqrt ((p1.x - p2.x)^2 + (p1.y - p2.y)^2)
row> distance {x = 0, y = 0} {x = 3, y = 4}
```

### Exercise 5: Variants

Handle variants:
```
row> :let mapOk = λf. λv. case v of
       <ok = x> -> <ok = f x>
       <other = x> -> <other = x>
row> mapOk (λn. n + 1) (<ok = 41>)
```

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected '|'`

**Solution**: Ensure `|` is in record/row context: `{l = v | r}` or `(l: T | ρ)`.

### Type Errors

**Problem**: "Label not found in row"

**Solutions**:
1. Ensure the field exists in the record type
2. Make function row-polymorphic: `∀ρ. {l: T | ρ} -> ...`

### Duplicate Labels

**Problem**: "Duplicate label in extension"

**Solution**: Remove field first: `{l = v | r \ l}` instead of `{l = v | r}`.

### Row Variable Scope

**Problem**: "Row variable not in scope"

**Solution**: Add `∀ρ.` quantification: `∀ρ. {l: T | ρ} -> ...`

## Comparison with Other Systems

### vs Structural Subtyping

| Feature | Row Polymorphism | Subtyping |
|---------|------------------|-----------|
| Mechanism | `∀ρ. {l: T | ρ}` | `{l: T, ...} <: {l: T}` |
| Inference | Full | Limited |
| Flexibility | High | Medium |
| Complexity | Medium | High |

### vs Nominal Types

| Feature | Row Polymorphism | Nominal Types |
|---------|------------------|---------------|
| Flexibility | High | Low |
| Safety | High | High |
| Boilerplate | Low | High |
| Duck typing | Yes (typed!) | No |

## Real Language Examples

### PureScript

```purescript
row> -- In PureScript:
row> -- type Point r = {x :: Number, y :: Number | r}
row> -- distance :: forall r. Point r -> Number

row> :type λp. sqrt (p.x * p.x + p.y * p.y)
  ∀ρ. {x: Nat, y: Nat | ρ} -> Nat
```

### Elm

```elm
row> -- In Elm:
row> -- type alias Point a = {a | x : Float, y : Float}
row> -- distance : Point a -> Float

row> :type λp. sqrt (p.x * p.x + p.y * p.y)
  ∀ρ. {x: Nat, y: Nat | ρ} -> Nat
```

### OCaml (Polymorphic Variants)

```ocaml
row> -- In OCaml:
row> -- let handle = function `Ok n -> n | `Error _ -> 0 | _ -> -1

row> :let handle = λv. case v of
       <ok = n> -> n
       <error = _> -> 0
       <other = _> -> -1
  handle : ∀ρ. <ok: Nat | error: String | ρ> -> Nat
```

## Performance Considerations

### Record Operations

```
-- Fast: direct field access
row> r.x

-- Fast: extension (just add to map)
row> {z = 5 | r}

-- Fast: restriction (remove from map)
row> r \ x

-- Slower: update (remove + add)
row> {x = newX | r \ x}
```

### Type Inference

Row unification can be expensive:
- Simple cases: O(n) where n is number of fields
- Complex cases: May require backtracking
- Use explicit type annotations to help inference

## Tips and Tricks

### 1. Use Row Polymorphism Liberally

```
-- Don't overconstrain
bad : {x: Nat, y: Nat} -> Nat
bad r = r.x + r.y

-- Better: allow extra fields
good : ∀ρ. {x: Nat, y: Nat | ρ} -> Nat
good r = r.x + r.y
```

### 2. Update with Remove-Then-Add

```
row> :let update = λl. λv. λr. {l = v | r \ l}
```

Always remove before adding to avoid duplicates.

### 3. Use Type Annotations for Clarity

```
row> (<ok = 42> : <ok: Nat | error: String>)
```

Help inference by annotating variant types.

### 4. Leverage Composability

```
row> :let addId = λn. λr. {id = n | r}
row> :let addTs = λt. λr. {timestamp = t | r}
row> :let enriched = addTs 1234 (addId 1 base)
```

Compose extensions incrementally.

## Further Reading

- [Chapter 14 README](README.md) - Complete theory
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step guide
- Wand (1987) - Row polymorphism for objects
- Rémy (1989) - Row types for ML

## Next Steps

After mastering the row types REPL:
- Chapter 15: Recursive Types (self-referential types)
- Advanced: Effect rows, scoped labels, gradual rows
- Practice: Use row types in PureScript or Elm

Enjoy exploring row polymorphism! 🎉
