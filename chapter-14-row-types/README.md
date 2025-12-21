# Chapter 14: Row Types & Extensible Records

## Overview

This chapter introduces **row polymorphism**, a powerful type system feature that
enables extensible records and polymorphic variants. Row types allow functions to
operate on records with "at least" certain fields, without specifying all fields
upfront—enabling a form of structural subtyping with full type inference.

## Learning Objectives

By the end of this chapter, you will:
- Understand row types and row polymorphism
- Work with extensible records (add, remove, access fields)
- Use polymorphic variants (open sum types)
- Write row-polymorphic functions
- See the connection to structural typing and duck typing

## Key Concepts

### 1. The Problem with Nominal Records

In most languages, record types are "closed":

```
type Person = {name: String, age: Nat}
type Employee = {name: String, age: Nat, salary: Nat}
```

A function `getName : Person -> String` can't accept an `Employee`, even though
`Employee` has all the required fields. Row polymorphism solves this.

### 2. Row Types

A **row** is a mapping from labels to types, possibly with a "tail" variable:

```
ρ ::= ()                    -- Empty row
    | (l: T | ρ)            -- Label l with type T, rest is ρ
    | α                     -- Row variable (unknown fields)
```

Key insight: `{x: Nat | α}` means "a record with at least field x: Nat, plus
whatever other fields α represents."

### 3. Row Polymorphism

Functions can be polymorphic over unknown fields:

```
getName : ∀ρ. {name: String | ρ} -> String
getName = λr. r.name
```

This function works with ANY record containing a `name` field:
- `getName {name = "Alice"}` ✓
- `getName {name = "Bob", age = 30}` ✓
- `getName {name = "Carol", age = 25, dept = "Sales"}` ✓

### 4. Record Operations

**Projection** (field access):
```
r.l : T   where r : {l: T | ρ}
```

**Extension** (adding a field):
```
{l = t | r} : {l: T | ρ}   where t : T and r : {ρ}
```

**Restriction** (removing a field):
```
r \ l : {ρ}   where r : {l: T | ρ}
```

### 5. Polymorphic Variants

Dual to extensible records, **polymorphic variants** are open sum types:

```
<l: T | ρ>   -- Variant with at least constructor l : T
```

Functions can handle "at least" certain cases:
```
handleNum : ∀ρ. <int: Nat | float: Nat | ρ> -> Nat
handleNum = λv. case v of
  <int = n> -> n
  <float = n> -> n
  <other = x> -> 0
```

## Syntax

### Types

```
T ::= Bool | Nat | Unit     -- Base types
    | T₁ -> T₂              -- Functions
    | {ρ}                   -- Record type
    | <ρ>                   -- Variant type
    | ∀α. T                 -- Row polymorphism

ρ ::= ()                    -- Empty row
    | (l: T | ρ)            -- Row extension
    | α                     -- Row variable
```

### Terms

```
t ::= {l₁=t₁, l₂=t₂, ...}   -- Record literal
    | t.l                   -- Projection
    | {l=t | r}             -- Record extension
    | r \ l                 -- Record restriction
    | <l=t> : T             -- Variant injection
    | case t of <l=x> -> t₁ | ...   -- Case analysis
    | Λα. t                 -- Row abstraction
    | t [ρ]                 -- Row application
```

## Type System

### Key Typing Rules

**Record Projection:**
```
   Γ ⊢ r : {l: T | ρ}
  ────────────────────
     Γ ⊢ r.l : T
```

**Record Extension:**
```
   Γ ⊢ r : {ρ}    Γ ⊢ t : T    l ∉ ρ
  ──────────────────────────────────
       Γ ⊢ {l = t | r} : {l: T | ρ}
```

**Row Polymorphism:**
```
      Γ ⊢ t : T    α ∉ FV(Γ)
  ───────────────────────────
     Γ ⊢ Λα. t : ∀α. T
```

### Row Unification

Row types require special unification rules:
- `{l: T | ρ₁} ~ {l: T | ρ₂}` when `ρ₁ ~ ρ₂`
- `{l₁: T₁ | ρ} ~ {l₂: T₂ | ρ'}` when `l₁ ≠ l₂`, by row reordering

This is where row types get interesting—labels can appear in any order!

## Examples

### Row-Polymorphic Functions

```
-- Works with any record having 'x' and 'y' fields
magnitude : ∀ρ. {x: Nat, y: Nat | ρ} -> Nat
magnitude = λp. sqrt (p.x * p.x + p.y * p.y)

-- Usage:
magnitude {x = 3, y = 4}                    -- OK: 5
magnitude {x = 0, y = 1, z = 2}             -- OK: 1
magnitude {x = 1, y = 2, label = "point"}  -- OK
```

### Record Update Pattern

```
-- Update a single field, preserving others
setName : ∀ρ. String -> {name: String | ρ} -> {name: String | ρ}
setName = λnewName. λr. {name = newName | r \ name}
```

### Safe Record Extension

```
-- Only extend if label is absent (type-level check)
extend : ∀ρ. (l ∉ ρ) => T -> {ρ} -> {l: T | ρ}
```

### Polymorphic Variant Handlers

```
-- Handle some cases, leave others open
type Result α ρ = <ok: α | error: String | ρ>

handleResult : ∀α ρ. Result α ρ -> (α -> β) -> (String -> β) ->
               <ρ> -> β
```

## Implementation Highlights

### Row Operations (TypeCheck.hs)

```haskell
-- Check if a label exists in a row
rowHas :: Label -> Row -> Bool
rowHas l RowEmpty = False
rowHas l (RowExtend l' _ rest)
  | l == l' = True
  | otherwise = rowHas l rest
rowHas l (RowVar _) = False  -- Unknown: conservatively false

-- Get type of a label in a row
rowGet :: Label -> Row -> Maybe Type
rowGet l (RowExtend l' ty rest)
  | l == l' = Just ty
  | otherwise = rowGet l rest
rowGet _ _ = Nothing

-- Extend a row with a new label
rowExtend :: Label -> Type -> Row -> Row
rowExtend = RowExtend
```

### Evaluation (Eval.hs)

```haskell
-- Record projection
TmProj (TmRecord fields) l
  | Just v <- Map.lookup l fields -> Just v

-- Record extension: add new field
TmExtend (TmRecord fields) l v
  | isValue v -> Just $ TmRecord (Map.insert l v fields)

-- Record restriction: remove field
TmRestrict (TmRecord fields) l
  -> Just $ TmRecord (Map.delete l fields)
```

## Connections to Real Languages

| Language | Feature | Notes |
|----------|---------|-------|
| **PureScript** | Full row polymorphism | Records and effects |
| **Elm** | Extensible records | Limited (no restriction) |
| **OCaml** | Polymorphic variants | `[> \`A of int \| \`B]` syntax |
| **TypeScript** | Structural typing | Similar feel, different mechanism |
| **Python** | Duck typing | Runtime version of row polymorphism |
| **Ur/Web** | Row types | Records, variants, and more |

## Theoretical Background

### Rows as Finite Maps

Mathematically, a row is a partial function from labels to types:
```
ρ : Label ⇀ Type
```

Row polymorphism allows abstracting over the "rest" of this map.

### Relationship to Subtyping

Row polymorphism provides similar expressiveness to width subtyping for records:
- Subtyping: `{x: Nat, y: Nat} <: {x: Nat}`
- Row poly: `{x: Nat | ρ}` instantiated with `ρ = (y: Nat)`

But row polymorphism has better type inference properties!

### Lack Constraints

Some systems add "lacks" constraints:
```
f : ∀ρ. (l ∉ ρ) => {ρ} -> {l: T | ρ}
```

This ensures we don't add a duplicate field.

## Running the Code

```bash
# Build the project
stack build

# Run the REPL
stack exec row-repl

# Run tests
stack test
```

### REPL Examples

```
row> :type {x = 0, y = true}
{x: Nat, y: Bool}

row> {x = 0, y = true}.x
0

row> :type λr. r.name
∀ρ. {name: α | ρ} -> α
```

## Exercises

See `exercises/EXERCISES.md` for practice problems covering:
1. Row-polymorphic function writing
2. Record extension and restriction
3. Polymorphic variant handling
4. Encoding objects with row types
5. Comparison with structural subtyping

## Further Reading

### Foundational Papers

- **Wand, "Complete Type Inference for Simple Objects" (1987)**
  Introduces row polymorphism for object types.
  [Semantic Scholar](https://www.semanticscholar.org/paper/Complete-Type-Inference-for-Simple-Objects-Wand/d96b2107c9aa8bb68f5e27a07cdcbf5ce3d07d43) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=16099086070638748683)

- **Rémy, "Type Inference for Records in a Natural Extension of ML" (1989)**
  Row polymorphism for ML-style records.
  [HAL](https://hal.science/inria-00075129/) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=7410270044612679060)

- **Cardelli & Mitchell, "Operations on Records" (1991)**
  Theoretical foundations of record operations.
  [ACM DL](https://dl.acm.org/doi/10.1145/96709.96714) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=6274156804039661065)

### Modern Treatments

- **Leijen, "Extensible Records with Scoped Labels" (2005)**
  Scoped labels for handling duplicate fields.
  [Microsoft Research](https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=10840446059383353929)

- **Lindley & Cheney, "Row-based Effect Types for Database Integration" (2012)**
  Row types for effect tracking.
  [ACM DL](https://dl.acm.org/doi/10.1145/2103786.2103798) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=17287101523988356316)

- **Hillerström & Lindley, "Liberating Effects with Rows and Handlers" (2016)**
  Combining row types with algebraic effects.
  [ACM DL](https://dl.acm.org/doi/10.1145/2976022.2976033) |
  [Google Scholar](https://scholar.google.com/scholar?cluster=5312148128218498295)

### Implementations

- [PureScript documentation on row polymorphism](https://github.com/purescript/documentation/blob/master/language/Types.md#rows)
- [Koka language documentation](https://koka-lang.github.io/koka/doc/index.html) (row-based effects)
- [Links language](https://links-lang.org/) (row types for web programming)

## Connection to Other Chapters

- **Chapter 9 (Subtyping):** Row polymorphism as alternative to width subtyping
- **Chapter 12 (Effect Systems):** Effect rows use similar machinery
- **Chapter 13 (Gradual Typing):** Gradual rows combine both ideas

## Project Structure

```
chapter-14-row-types/
├── src/
│   ├── Syntax.hs      -- Types, rows, terms
│   ├── TypeCheck.hs   -- Row-aware type checking
│   ├── Eval.hs        -- Record/variant operations
│   ├── Parser.hs      -- Syntax for rows
│   └── Pretty.hs      -- Pretty printing
├── app/
│   └── Main.hs        -- REPL
├── test/
│   └── Spec.hs        -- Test suite (65 tests)
├── exercises/
│   └── EXERCISES.md   -- Practice exercises
├── package.yaml
├── stack.yaml
└── README.md
```
