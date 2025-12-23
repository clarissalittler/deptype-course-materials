# Chapter 14: Row Types & Extensible Records - Quick Start

## TL;DR (30 seconds)

Row polymorphism lets functions work with records having "at least" certain fields - like duck typing with static types! Use `{x: Nat | ρ}` to mean "has x, plus unknown fields ρ". This chapter teaches structural polymorphism with full type inference. In 5 minutes, you'll write your first row-polymorphic function!

**Who**: Anyone who knows basic type systems and records (Chapter 2)
**Time**: 2-3 weeks (or 1 intensive week)
**Payoff**: Understand PureScript, Elm extensible records, and structural typing

## What You'll Learn

- Row types and row polymorphism
- Extensible records (add, remove, access fields)
- Polymorphic variants (open sum types)
- Connection to structural typing
- Application to effect systems

**Tangible Outcome**: Write reusable functions that work with ANY record structure!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-14-row-types
stack build
stack exec row-repl
```

You should see:
```
Welcome to the Row Types REPL!
row>
```

### Step 2: Your First Extensible Record (1 minute)

```
row> {x = 3, y = 4}
{x = 3, y = 4}

row> :type {x = 3, y = 4}
{x: Nat, y: Nat}
```

A record with two fields!

### Step 3: Row-Polymorphic Function (1 minute)

```
row> :type λr. r.x
∀ρ. {x: α | ρ} -> α
```

This works with ANY record containing field `x`!

### Step 4: It Really Works! (1 minute)

```
row> :let getX = λr. r.x
getX : ∀ρ. {x: Nat | ρ} -> Nat

row> getX {x = 5}
5

row> getX {x = 10, y = 20}
10

row> getX {x = 42, y = true, z = "hello"}
42
```

**Achievement Unlocked**: You just wrote a function that works with infinite different record types! 🎉

## Your First Success - Understanding Row Types (10 minutes)

### 1. The Record Problem

Traditional records are too rigid:

```
-- Closed record type
type Point = {x: Nat, y: Nat}

distance : Point -> Nat
distance p = sqrt (p.x * p.x + p.y * p.y)

-- Won't work with 3D points!
distance {x = 3, y = 4, z = 5}  -- ERROR
```

### 2. Row-Polymorphic Solution

```
row> :type λp. sqrt (p.x * p.x + p.y * p.y)
∀ρ. {x: Nat, y: Nat | ρ} -> Nat

row> :let distance = λp. sqrt (p.x * p.x + p.y * p.y)

row> distance {x = 3, y = 4}
5

row> distance {x = 3, y = 4, z = 5}
5

row> distance {x = 0, y = 1, color = "red"}
1
```

It works with 2D, 3D, or ANY record with x and y!

### 3. Record Operations

```
-- Access field
row> {x = 3, y = 4}.x
3

-- Add field
row> {z = 5 | {x = 3, y = 4}}
{x = 3, y = 4, z = 5}

-- Remove field
row> {x = 3, y = 4} \ x
{y = 4}
```

**Achievement Unlocked**: You understand extensible records! 🎉

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - step-by-step examples
2. Follow `LESSON_PLAN.md` - structured 12-16 hour course
3. Use `REPL_GUIDE.md` for interactive exploration
4. Try exercises 1-5 in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (45 minutes)
2. Work through exercises 1-10 (3-4 hours)
3. Check solutions in `exercises/Solutions.hs`
4. Take `QUIZ.md` to verify understanding

### For Practitioners
1. Read "Row Polymorphism" section in README
2. Study PureScript examples
3. Model your domain with extensible records
4. Explore polymorphic variants

## When to Skip This Chapter

**Skip if**:
- You only need simple, closed record types
- You never work with structural typing
- You've studied row polymorphism before

**Don't skip if**:
- You use PureScript, Elm, or OCaml
- You want flexible, reusable code
- You're interested in effect systems
- You like structural typing (duck typing with types!)

## Core Concepts (10 minutes)

### Row Types

A **row** is a mapping from labels to types:

```
()                   Empty row
(x: Nat | ())        Just field x
(x: Nat | (y: Bool | ()))  Fields x and y
(x: Nat | ρ)         Field x, plus unknown row ρ
```

### Record Types from Rows

Wrap a row in braces `{}`:

```
{}                   Empty record
{x: Nat}             Just x field
{x: Nat, y: Bool}    Both x and y
{x: Nat | ρ}         At least x (open record!)
```

### Row Polymorphism

Use `∀ρ.` to abstract over unknown fields:

```
getName : ∀ρ. {name: String | ρ} -> String
getName r = r.name
```

Works with ANY record containing `name`!

### Polymorphic Variants

Dual to records (open sum types):

```
<ok: Nat | ρ>        At least ok case
<error: String | ρ>  At least error case
```

## Quick Reference

```bash
# Build
cd chapter-14-row-types && stack build

# Run REPL
stack exec row-repl

# Essential REPL Commands
:help               # Show all commands
:type <term>        # Show type
:eval <term>        # Evaluate term
:expand <type>      # Expand row type
:quit               # Exit

# Syntax
{x = 3, y = 4}      # Record literal
r.x                 # Field access
{z = 5 | r}         # Add field z
r \ x               # Remove field x
λr. r.name          # Row-polymorphic function
∀ρ. {x: T | ρ}      # Row type (at least x)
<ok = 42>           # Variant injection
```

## Example Session

```
row> :type {x = 3, y = 4}
{x: Nat, y: Nat}

row> :type λr. r.name
∀ρ. {name: α | ρ} -> α

row> {z = 5 | {x = 3, y = 4}}
{x = 3, y = 4, z = 5}

row> {x = 3, y = 4} \ x
{y = 4}

row> :type λr. {age = 30 | r}
∀ρ. {ρ} -> {age: Nat | ρ}

row> :let addAge = λn. λr. {age = n | r}

row> addAge 25 {name = "Alice"}
{name = "Alice", age = 25}
```

## Success Criteria

You're ready for the next chapter when you can:
- [ ] Explain row types and row variables
- [ ] Write row-polymorphic functions
- [ ] Use record operations (project, extend, restrict)
- [ ] Understand polymorphic variants
- [ ] See connection to structural typing

**Minimum**: Understand row polymorphism and basic operations
**Ideal**: Complete exercises 1-10 and understand variants

## Time Investment

- **Minimum**: 4 hours (core concepts only)
- **Recommended**: 12-16 hours (solid understanding)
- **Complete**: 24 hours (all exercises + advanced topics)

## Common Pitfalls

### Pitfall 1: Forgetting Row Variable
```
-- Wrong: closed record
getX : {x: Nat} -> Nat

-- Right: row-polymorphic
getX : ∀ρ. {x: Nat | ρ} -> Nat
```

### Pitfall 2: Duplicate Extension
```
-- Error! x already exists
{x = 5 | {x = 3, y = 4}}

-- Correct: remove first
{x = 5 | {x = 3, y = 4} \ x}
```

### Pitfall 3: Assuming Order
```
-- These ARE equal!
{x: Nat, y: Bool} = {y: Bool, x: Nat}
```

Order doesn't matter in row types!

### Pitfall 4: Closed vs Open
```
-- Closed: ONLY x and y
{x: Nat, y: Bool}

-- Open: at least x and y
{x: Nat, y: Bool | ρ}
```

## Real-World Examples

### PureScript
```purescript
type Point r = {x :: Number, y :: Number | r}

distance :: forall r. Point r -> Number
distance p = sqrt (p.x * p.x + p.y * p.y)
```

### Elm
```elm
type alias Point a = {a | x : Float, y : Float}

distance : Point a -> Float
distance p = sqrt (p.x * p.x + p.y * p.y)
```

### OCaml (Polymorphic Variants)
```ocaml
let handle = function
  | `Ok n -> n
  | `Error _ -> 0
  | _ -> -1  (* other cases *)
```

## Help & Resources

- **Stuck on rows?** Check `CHEAT_SHEET.md` for quick reference
- **Need examples?** See `TUTORIAL.md` for walkthroughs
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Practice**: `PRACTICE_PROBLEMS.md` has 25+ problems

## Connection to Other Chapters

- **Chapter 9 (Subtyping)**: Row polymorphism vs width subtyping
- **Chapter 12 (Effect Systems)**: Effect rows use same machinery
- **Chapter 6 (Polymorphism)**: Row variables are like type variables

## What Makes This Chapter Special

Row types are **practical type theory**:
- PureScript uses them extensively
- Elm has extensible records
- OCaml has polymorphic variants
- Effect systems rely on row types
- Better inference than subtyping

Unlike nominal typing, row types embrace **structural polymorphism** - if it has the right shape, it works!

## Your First Exercise

Try this now:

```
row> :let fullName = λr. r.first ++ " " ++ r.last
row> fullName {first = "Alice", last = "Smith"}
```

What's the type of `fullName`?

<details>
<summary>Answer</summary>

Type: `∀ρ. {first: String, last: String | ρ} -> String`

Explanation:
- Requires both `first` and `last` fields
- Works with any record having at least these fields
- Returns concatenated string
- Row variable `ρ` represents any additional fields
</details>

## Cool Examples to Try

### Example 1: 2D/3D Points
```
row> :let magnitude = λp. sqrt (p.x * p.x + p.y * p.y)

row> magnitude {x = 3, y = 4}
5

row> magnitude {x = 3, y = 4, z = 5}
5  -- Ignores z!
```

### Example 2: Adding Fields
```
row> :let addId = λn. λr. {id = n | r}

row> addId 1 {name = "Alice"}
{id = 1, name = "Alice"}

row> addId 2 {name = "Bob", age = 30}
{id = 2, name = "Bob", age = 30}
```

### Example 3: Updating Fields
```
row> :let setName = λname. λr. {name = name | r \ name}

row> setName "Carol" {name = "Bob", age = 30}
{name = "Carol", age = 30}
```

### Example 4: Polymorphic Variants
```
row> :let handleOk = λv. case v of
       <ok = n> -> n
       <other = _> -> 0

row> handleOk (<ok = 42> : <ok: Nat | ρ>)
42

row> handleOk (<error = "fail"> : <ok: Nat | error: String | ρ>)
0
```

## Comparison: Closed vs Open

### Closed (Traditional)
```
type Person = {name: String, age: Nat}

greet : Person -> String
greet p = "Hello, " ++ p.name

-- Won't work:
greet {name = "Alice", age = 30, email = "a@example.com"}  -- ERROR
```

### Open (Row Polymorphic)
```
greet : ∀ρ. {name: String | ρ} -> String
greet p = "Hello, " ++ p.name

-- Works with anything:
greet {name = "Alice"}                                       ✓
greet {name = "Bob", age = 30}                              ✓
greet {name = "Carol", age = 25, email = "c@example.com"}   ✓
```

## Why Row Types Matter

1. **Code Reuse**: One function works with many record types
2. **Type Safety**: Still statically typed (unlike duck typing)
3. **Inference**: Full type inference (unlike subtyping)
4. **Composability**: Easily combine different extensions
5. **Effects**: Foundation for effect system type tracking

## Next Chapter Preview

Chapter 15 covers recursive types - types that reference themselves. Combined with row types, you can model complex recursive structures with structural flexibility!

Ready to make your types structural and flexible? Let's go! 🚀
