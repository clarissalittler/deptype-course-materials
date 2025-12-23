# Chapter 9: Subtyping REPL User Guide

## Overview

The Subtyping REPL provides an interactive environment for experimenting with subtyping, type checking, and record types.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-09-subtyping
stack build

# Run the REPL
stack exec subtyping-repl
```

### Quick Start

```
subtype> \x:Nat. x
  \x:Nat. x : Nat -> Nat

subtype> :type {x = 0, y = true}
  {x: Nat, y: Bool}

subtype> :subtype Bool Top
  Bool <: Top ✓
```

## Features

### 1. Type Checking

Type check terms to see their types:

```
subtype> true
  true : Bool

subtype> \x:Top. x
  \x:Top. x : Top -> Top

subtype> {x = 0, y = true}
  {x = 0, y = true} : {x: Nat, y: Bool}

subtype> (\p:{x: Nat}. p.x) {x = 5, y = true}
  5 : Nat
```

### 2. Subtyping Checks

Check subtyping relationships explicitly:

```
subtype> :subtype Bool Top
  Bool <: Top ✓

subtype> :subtype Top Bool
  Top <: Bool ✗

subtype> :subtype {x: Nat, y: Bool} {x: Nat}
  {x: Nat, y: Bool} <: {x: Nat} ✓

subtype> :subtype (Top -> Nat) (Bool -> Nat)
  (Top -> Nat) <: (Bool -> Nat) ✓
```

### 3. Record Operations

#### Creating Records

```
subtype> {x = 0, y = true, z = false}
  {x = 0, y = true, z = false} : {x: Nat, y: Bool, z: Bool}
```

#### Field Projection

```
subtype> {x = 5, y = 10}.x
  5 : Nat

subtype> {name = true, age = 0}.name
  true : Bool
```

#### Width Subtyping

```
subtype> let getX = \p:{x: Nat}. p.x
subtype> getX {x = 5, y = 10, z = 15}
  5 : Nat
```

The record `{x: Nat, y: Nat, z: Nat}` is a subtype of `{x: Nat}`, so this works!

### 4. Function Subtyping (Contravariance)

#### Basic Example

```
subtype> let acceptTop = \x:Top. 0
subtype> :type acceptTop
  Top -> Nat

subtype> :subtype (Top -> Nat) (Bool -> Nat)
  (Top -> Nat) <: (Bool -> Nat) ✓
```

A function accepting `Top` can be used where a function accepting `Bool` is expected.

#### Higher-Order Example

```
subtype> let apply = \f:(Bool -> Nat). \x:Bool. f x
subtype> let topToNat = \x:Top. 0

subtype> apply topToNat true
  0 : Nat
```

This works because `Top -> Nat <: Bool -> Nat`.

### 5. Top and Bot Types

#### Top Type

```
subtype> :subtype Nat Top
  Nat <: Top ✓

subtype> :subtype Bool Top
  Bool <: Top ✓

subtype> :subtype {x: Nat} Top
  {x: Nat} <: Top ✓
```

Every type is a subtype of Top.

#### Bot Type

```
subtype> :subtype Bot Nat
  Bot <: Nat ✓

subtype> :subtype Bot Bool
  Bot <: Bool ✓

subtype> :subtype Bot {x: Nat}
  Bot <: {x: Nat} ✓
```

Bot is a subtype of every type (but has no values).

### 6. Ascription (Explicit Upcasting)

```
subtype> true as Top
  true as Top : Top

subtype> {x = 0, y = true} as {x: Nat}
  {x = 0, y = true} as {x: Nat} : {x: Nat}

subtype> (\x:Top. 0) as (Bool -> Nat)
  (\x:Top. 0) as (Bool -> Nat) : Bool -> Nat
```

Ascription allows explicit upcasting to a supertype.

**Important**: Downcasting is NOT allowed:

```
subtype> 0 as Bool
  Type error: Nat is not a subtype of Bool
```

### 7. Conditionals with Join

The type of `if-then-else` is the **join** of the branch types:

```
subtype> if true then 0 else 1
  0 : Nat

subtype> if true then {x = 0, y = true} else {x = 1, z = false}
  {x = 0} : {x: Nat}
```

Only the common field `x` is kept!

#### Join Examples

```
# Same type - no join needed
subtype> if true then true else false
  true : Bool

# Different record types - join to common fields
subtype> if true
          then {a = 0, b = true, c = false}
          else {a = 1, b = false}
  {a = 0, b = false} : {a: Nat, b: Bool}

# Incompatible types - join to Top
subtype> if true then 0 else true
  0 : Top
```

### 8. Depth Subtyping

Field types can be subtypes:

```
subtype> :subtype {x: Bot} {x: Nat}
  {x: Bot} <: {x: Nat} ✓

subtype> :subtype {f: Top -> Bot} {f: Bool -> Nat}
  {f: Top -> Bot} <: {f: Bool -> Nat} ✓
```

### 9. Combining Width and Depth

```
subtype> :subtype {x: Bot, y: Nat, extra: Bool} {x: Nat, y: Top}
  {x: Bot, y: Nat, extra: Bool} <: {x: Nat, y: Top} ✓
```

This works because:
- Width: `extra` field is dropped
- Depth: `Bot <: Nat` and `Nat <: Top`

## Command Reference

### Evaluation Commands

| Command | Description |
|---------|-------------|
| `<expr>` | Evaluate and type check an expression |
| `:type <expr>` | Show only the type (alias: `:t`) |
| `:eval <expr>` | Show only the value (alias: `:e`) |

### Subtyping Commands

| Command | Description |
|---------|-------------|
| `:subtype T1 T2` | Check if T1 <: T2 (alias: `:sub`, `:s`) |
| `:join T1 T2` | Compute T1 ⊔ T2 (least upper bound) |
| `:meet T1 T2` | Compute T1 ⊓ T2 (greatest lower bound) |

### Information Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help message (alias: `:h`, `:?`) |
| `:examples` | Show example terms (alias: `:ex`) |
| `:quit` | Exit the REPL (alias: `:q`, `:exit`) |

## Syntax Reference

### Terms

```
t ::= x                       -- Variable
    | \x:T. t                 -- Abstraction
    | t1 t2                   -- Application
    | true | false            -- Booleans
    | if t1 then t2 else t3   -- Conditional
    | 0 | succ t | pred t     -- Natural numbers
    | iszero t                -- Zero test
    | {l1 = t1, ..., ln = tn} -- Record
    | t.l                     -- Projection
    | t as T                  -- Ascription
```

### Types

```
T ::= Bool                    -- Boolean
    | Nat                     -- Natural number
    | T1 -> T2                -- Function
    | Top                     -- Top type
    | Bot                     -- Bottom type
    | {l1: T1, ..., ln: Tn}   -- Record
```

## Advanced Examples

### Example 1: OOP-Style Class Hierarchy

```
subtype> -- Define "classes" as record types
subtype> let vehicle = {wheels = 4}
subtype> let car = {wheels = 4, doors = 4}
subtype> let truck = {wheels = 6, doors = 2, cargo = 1000}

subtype> -- Function accepting any vehicle
subtype> let printWheels = \v:{wheels: Nat}. v.wheels

subtype> printWheels vehicle
  4 : Nat

subtype> printWheels car
  4 : Nat

subtype> printWheels truck
  6 : Nat
```

All work due to width subtyping!

### Example 2: Contravariant Higher-Order Functions

```
subtype> let twice = \f:(Nat -> Nat). \x:Nat. f (f x)
subtype> let constZero = \x:Top. 0

subtype> :subtype (Top -> Nat) (Nat -> Nat)
  (Top -> Nat) <: (Nat -> Nat) ✓

subtype> twice constZero 5
  0 : Nat
```

### Example 3: Record Depth with Functions

```
subtype> let handler = {handle = \x:Top. 0}
subtype> :type handler
  {handle: Top -> Nat}

subtype> :subtype {handle: Top -> Nat} {handle: Bool -> Nat}
  {handle: Top -> Nat} <: {handle: Bool -> Nat} ✓

subtype> (handler as {handle: Bool -> Nat}).handle true
  0 : Nat
```

### Example 4: Join in Conditionals

```
subtype> let makePoint = \isOrigin:Bool.
           if isOrigin
             then {x = 0, y = 0, origin = true}
             else {x = 5, y = 10}

subtype> :type makePoint
  Bool -> {x: Nat, y: Nat}
```

The `origin` field is lost in the join!

### Example 5: Complex Variance

```
subtype> :subtype ((Top -> Bot) -> Nat) ((Bool -> Nat) -> Bool)
  ((Top -> Bot) -> Nat) <: ((Bool -> Nat) -> Bool) ✗

# Let's check why:
# Argument: Need (Bool -> Nat) <: (Top -> Bot)
#   - Arg: Need Top <: Bool? No!
# Fails at the contravariant argument position
```

### Example 6: Meet of Records

```
subtype> :meet {x: Nat} {y: Bool}
  {x: Nat, y: Bool}

subtype> :meet {x: Nat, y: Bool} {x: Bool, z: Top}
  {x: Bot, y: Bool, z: Top}
```

Meet combines all fields, taking the meet of field types.

## Common Patterns

### Pattern 1: Generic Field Access

```
subtype> let getName = \obj:{name: Bool}. obj.name
subtype> getName {name = true, age = 25}
subtype> getName {name = false, address = true, phone = false}
```

Works for any record with a `name` field!

### Pattern 2: Flexible Function Arguments

```
subtype> let applyToTrue = \f:(Bool -> Nat). f true
subtype> applyToTrue (\x:Top. 0)      -- Top -> Nat <: Bool -> Nat
subtype> applyToTrue (\x:Bool. 0)     -- Bool -> Nat <: Bool -> Nat
```

### Pattern 3: Upcasting for API Boundaries

```
subtype> let internal = {x = 0, y = true, secret = false}
subtype> let public = internal as {x: Nat, y: Bool}
subtype> :type public
  {x: Nat, y: Bool}
```

Hide the `secret` field via ascription.

### Pattern 4: Join for Flexible Returns

```
subtype> let makeRecord = \variant:Nat.
           if (iszero variant)
             then {tag = true, value = 0}
             else {tag = false, error = true}

subtype> :type makeRecord
  Nat -> {tag: Bool}
```

## Tips and Tricks

### 1. Understanding Contravariance

When confused about function subtyping, think from the **caller's perspective**:

```
# Caller provides: Dog
# Function expects: Animal
# Can function handle Dog? Yes! (Dog is an Animal)
# So: (Animal -> R) <: (Dog -> R)
```

### 2. Debugging Subtyping

Use `:subtype` to check your assumptions:

```
subtype> :subtype {x: Nat, y: Bool} {x: Nat}
  ✓

subtype> :subtype {x: Nat} {x: Nat, y: Bool}
  ✗
```

### 3. Exploring Join

Use `:join` to understand conditional types:

```
subtype> :join {x: Nat, y: Bool} {x: Nat, z: Top}
  {x: Nat}

subtype> :join (Nat -> Bool) (Bool -> Nat)
  Bot -> Top
```

### 4. Finding Common Supertypes

To find a common supertype for an if-then-else:

```
subtype> :join {id = 0, name = true} {id = 1, age = 25}
  {id: Nat}
```

Only `id` is common!

### 5. Variance Calculation

Count arrows to the left:
- Even number (0, 2, 4, ...) → Covariant (+)
- Odd number (1, 3, 5, ...) → Contravariant (-)

```
X                      0 arrows → + (covariant)
A -> X                 0 arrows → + (covariant)
X -> B                 1 arrow  → - (contravariant)
(X -> A) -> B          2 arrows → + (covariant)
(A -> X) -> B          1 arrow  → - (contravariant)
```

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected '->'`

**Solution**: Use proper syntax `T1 -> T2`, not `T1 → T2` (unless Unicode is supported).

### Subtyping Failures

**Problem**: Expected subtyping doesn't hold.

**Solutions**:
1. Check direction: `{more fields} <: {fewer fields}`
2. For functions: remember contravariance
3. Use `:subtype` to debug

### Type Errors in Application

**Problem**: `Cannot apply function: argument type mismatch`

**Solution**: Check that argument type is a subtype of parameter type:

```
subtype> let f = \x:Nat. x
subtype> f true
  Type error: Bool is not a subtype of Nat
```

### Ascription Failures

**Problem**: `Cannot ascribe: not a subtype`

**Solution**: Ascription only allows upcasting (to supertypes):

```
subtype> 0 as Top      -- OK: Nat <: Top
subtype> 0 as Bool     -- ERROR: Nat ⊀ Bool
```

## Exercises

Try these in the REPL to learn subtyping:

### Exercise 1: Width Subtyping
Create a record with 5 fields, then define functions that work on subsets of fields.

### Exercise 2: Contravariance Exploration
Create a higher-order function and pass functions with more general argument types.

### Exercise 3: Join Investigation
Use `:join` to compute joins of:
- Different record types
- Function types
- Mixed types

### Exercise 4: Building a Type Hierarchy
Model an employee hierarchy:
- `Employee`: `{name: Bool}`
- `Manager`: `{name: Bool, department: Bool}`
- `Executive`: `{name: Bool, department: Bool, level: Nat}`

Show all subtyping relationships.

### Exercise 5: Variance Puzzle
For `((X -> Bool) -> Nat) -> Top`, determine the variance of `X`.

## Real-World Connections

### TypeScript Structural Typing

TypeScript uses structural subtyping like our system:

```typescript
interface Point { x: number; y: number }
function distance(p: Point) { ... }
distance({ x: 0, y: 0, color: "red" });  // OK!
```

This is width subtyping in action.

### Scala Variance Annotations

```scala
class List[+A]  // Covariant: List[Dog] <: List[Animal]
```

The `+` means covariant, which our system checks automatically.

### Liskov Substitution Principle

Barbara Liskov's principle states: subtypes must be substitutable for supertypes. Our subtyping rules enforce this!

## Further Reading

- [README.md](README.md) - Complete theory and formal semantics
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step tutorial
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- [COMMON_MISTAKES.md](COMMON_MISTAKES.md) - Avoid common errors
- Pierce's TAPL Chapters 15-17 - In-depth treatment

## Next Steps

After mastering subtyping:
- **Chapter 10**: Linear Types (resource usage tracking)
- **Bounded Quantification**: Combining subtyping with polymorphism
- **Intersection/Union Types**: More expressive type systems

Have fun exploring subtyping! Understanding variance and substitutability is key to modern type systems.
