# Chapter 11: REPL User Guide - Refinement Types

## Overview

The Refinement Types REPL provides an interactive environment for experimenting with refinement types, predicates, subtyping, and path-sensitive type checking.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-11-refinement-types
stack build

# Run the REPL
stack exec refinement-repl
```

### Quick Start

```
refinement> :type λx : {n : Nat | n > 0}. x
{n : Nat | n > 0} -> {n : Nat | n > 0}

refinement> :check 5 > 0
Valid (always true)

refinement> :help
[Shows available commands]
```

## Features

### 1. Type Checking with Refinements

Type check expressions with refinement type annotations:

```
refinement> :type λx : Nat. x
Nat -> Nat

refinement> :type λx : {n : Nat | n > 0}. x
{n : Nat | n > 0} -> {n : Nat | n > 0}

refinement> :type λx : {n : Nat | n > 0}. pred x
{n : Nat | n > 0} -> Nat
```

The REPL automatically checks that predicates are satisfied.

### 2. Predicate Validity Checking

Check if predicates are valid:

```
refinement> :check true
Valid (always true)

refinement> :check false
Invalid (always false)

refinement> :check 5 > 0
Valid (always true)

refinement> :check x > 0
Unknown (depends on x)
```

### 3. Subtyping Queries

Check subtyping relationships:

```
refinement> :subtype {x: Nat | x > 10} <: {x: Nat | x > 5}
true (x > 10 implies x > 5)

refinement> :subtype {x: Nat | x > 5} <: {x: Nat | x > 10}
false (x > 5 does not imply x > 10)

refinement> :subtype {x: Nat | x == 7} <: {x: Nat | x > 0}
true (7 > 0)
```

### 4. Expression Evaluation

Evaluate terms to values:

```
refinement> :eval 5 + 3
8

refinement> :eval if true then 1 else 2
1

refinement> :eval let x = 3 in x + x
6

refinement> :eval (λx : Nat. x + 1) 5
6
```

### 5. Path Sensitivity Exploration

See how conditions refine types:

```
refinement> :type λx : Nat. if iszero x then 0 else pred x
Nat -> Nat

refinement> :path λx : Nat. if x > 5 then x else x + 10
In then branch: x : {n: Nat | n > 5}
In else branch: x : {n: Nat | n <= 5}
Result type: Nat
```

## Common Refinement Patterns

### Positive Numbers

```
refinement> :let Pos = {n : Nat | n > 0}
Type alias: Pos = {n : Nat | n > 0}

refinement> :type λx : Pos. x
{n : Nat | n > 0} -> {n : Nat | n > 0}

refinement> :let safePred = λx : Pos. pred x
safePred : {n : Nat | n > 0} -> Nat
```

### Bounded Values

```
refinement> :let Digit = {n : Nat | n >= 0 && n <= 9}
Type alias: Digit = {n : Nat | n >= 0 && n <= 9}

refinement> :let Percent = {n : Nat | n >= 0 && n <= 100}
Type alias: Percent = {n : Nat | n >= 0 && n <= 100}
```

### Non-Zero Division

```
refinement> :let NonZero = {n : Nat | n > 0}
Type alias: NonZero = {n : Nat | n > 0}

refinement> :let safeDiv = λn : Nat. λd : NonZero. n `div` d
safeDiv : Nat -> {n : Nat | n > 0} -> Nat

refinement> :eval safeDiv 10 2
5

refinement> :eval safeDiv 10 0
Type error: 0 does not satisfy {n : Nat | n > 0}
```

### Singleton Types

```
refinement> :let OnlyTrue = {b : Bool | b == true}
Type alias: OnlyTrue = {b : Bool | b == true}

refinement> :let OnlyFive = {n : Nat | n == 5}
Type alias: OnlyFive = {n : Nat | n == 5}

refinement> :type (5 : OnlyFive)
{n : Nat | n == 5}

refinement> :type (6 : OnlyFive)
Type error: 6 does not satisfy n == 5
```

## Path Sensitivity Examples

### Simple Conditional

```
refinement> :type λx : Nat. if x > 0 then x else 0
Nat -> Nat

refinement> :path λx : Nat. if x > 0 then x else 0
In then branch: x : {n: Nat | n > 0}
In else branch: x : {n: Nat | n <= 0}
Both branches return: Nat
```

### Safe Predecessor

```
refinement> :let safePred = λx : Nat. if iszero x then 0 else pred x
safePred : Nat -> Nat

refinement> :eval safePred 5
4

refinement> :eval safePred 0
0
```

The type checker knows in the `else` branch that `x > 0`, making `pred x` safe!

### Nested Conditions

```
refinement> :type λx : Nat. if x > 10 then (if x < 20 then 1 else 2) else 0
Nat -> Nat

refinement> :path λx : Nat. if x > 10 then (if x < 20 then 1 else 2) else 0
Outer then branch: x : {n: Nat | n > 10}
  Inner then branch: x : {n: Nat | n > 10 && n < 20}
  Inner else branch: x : {n: Nat | n > 10 && n >= 20}
Outer else branch: x : {n: Nat | n <= 10}
```

### Multiple Comparisons

```
refinement> :type λx : Nat. λy : Nat. if x > y then x else y
Nat -> Nat -> Nat

refinement> :path λx : Nat. λy : Nat. if x > y then x else y
In then branch: Known: x > y
In else branch: Known: x <= y
Result: maximum of x and y
```

## Dependent Function Examples

### Replicate

```
refinement> :type replicate
(n: Nat) -> a -> {xs: List a | length xs == n}

refinement> :eval replicate 3 5
[5, 5, 5]
```

### Safe Index

```
refinement> :type index
(xs: List a) -> {i: Nat | i < length xs} -> a

refinement> :eval index [1, 2, 3] 1
2

refinement> :eval index [1, 2, 3] 5
Type error: 5 does not satisfy i < length xs
```

### Non-Empty Head

```
refinement> :type head
{xs: List a | length xs > 0} -> a

refinement> :eval head [1, 2, 3]
1

refinement> :eval head []
Type error: [] does not satisfy length xs > 0
```

## Advanced Features

### Implication Checking

```
refinement> :implies x > 10, x > 5
true (x > 10 implies x > 5)

refinement> :implies x > 5, x > 10
false (x > 5 does not imply x > 10)

refinement> :implies x == 7, x > 0
true (7 > 0)

refinement> :implies false, anything
true (false implies anything - vacuously true)
```

### Predicate Normalization

```
refinement> :normalize x > 0 && x > 0
x > 0

refinement> :normalize x > 0 && true
x > 0

refinement> :normalize x > 0 || false
x > 0

refinement> :normalize !(!x)
x
```

### Type Aliases

```
refinement> :let Pos = {n : Nat | n > 0}
refinement> :let NonNeg = {n : Nat | n >= 0}
refinement> :let Digit = {n : Nat | n >= 0 && n <= 9}

refinement> :aliases
Current type aliases:
  Pos = {n : Nat | n > 0}
  NonNeg = {n : Nat | n >= 0}
  Digit = {n : Nat | n >= 0 && n <= 9}
```

### Context Display

```
refinement> :context
Current typing context:
  [empty]

refinement> :let x = 5
refinement> :context
Current typing context:
  x : Nat
```

## Command Reference

### Type and Evaluation Commands

| Command | Description | Example |
|---------|-------------|---------|
| `:type <expr>` | Infer type of expression | `:type λx : Nat. x` |
| `:eval <expr>` | Evaluate expression | `:eval 5 + 3` |
| `:check <pred>` | Check predicate validity | `:check 5 > 0` |
| `:subtype <t1> <: <t2>` | Check subtyping | `:subtype Pos <: Nat` |

### Refinement-Specific Commands

| Command | Description | Example |
|---------|-------------|---------|
| `:implies <p>, <q>` | Check p ⟹ q | `:implies x > 5, x > 0` |
| `:normalize <pred>` | Simplify predicate | `:normalize x && true` |
| `:path <expr>` | Show path refinements | `:path if x > 0 then...` |

### Context Commands

| Command | Description | Example |
|---------|-------------|---------|
| `:let name = expr` | Define binding | `:let x = 5` |
| `:let Type = {refinement}` | Define type alias | `:let Pos = {n:Nat\|n>0}` |
| `:context` | Show typing context | `:context` |
| `:aliases` | Show type aliases | `:aliases` |
| `:clear` | Clear all bindings | `:clear` |

### Information Commands

| Command | Description |
|---------|-------------|
| `:help` | Show help message |
| `:examples` | Show example refinements |
| `:quit` | Exit the REPL |

## Syntax Guide

### Refinement Types

```
{x: T | φ}              Variable refinement
{n: Nat | n > 0}        Positive naturals
{b: Bool | b == true}   Only true
{xs: List a | length xs > 0}  Non-empty lists
```

### Predicates

```
# Boolean operations
true, false             Constants
!φ                      Negation
φ && ψ                  Conjunction
φ || ψ                  Disjunction
φ => ψ                  Implication

# Comparisons
a == b, a != b          Equality
a < b, a <= b           Ordering
a > b, a >= b           Ordering

# Arithmetic
a + b                   Addition
a - b                   Subtraction
n * a                   Scalar multiplication
```

### Dependent Functions

```
(x: T1) -> T2           Basic dependent type
(n: Nat) -> Vec a n     Vector of length n
(x: {n:Nat|n>0}) -> Nat Refined argument
```

## Practical Examples

### Example 1: Safe Array Access

```
refinement> :let Array = λn. {arr: [Nat] | length arr == n}
refinement> :let get = λarr. λi. arr !! i
refinement> :type get
(arr: Array n) -> {i: Nat | i < n} -> Nat

refinement> :eval let arr = [1,2,3] in get arr 1
2
```

### Example 2: Bounded Arithmetic

```
refinement> :let boundedInc = λx : {n:Nat|n<100}.
                               if x < 99 then x + 1 else x
boundedInc : {n:Nat|n<100} -> {m:Nat|m<=100}

refinement> :eval boundedInc 50
51

refinement> :eval boundedInc 99
99
```

### Example 3: State Machine

```
refinement> :let State = Nat
refinement> :let Closed = {s:State | s == 0}
refinement> :let Open = {s:State | s == 1}

refinement> :type λs : Closed. 1  -- open
Closed -> Nat

refinement> :type λs : Open. 0    -- close
Open -> Nat
```

### Example 4: Sorted Lists

```
refinement> :let Sorted = {xs: [Nat] | isSorted xs}
refinement> :type insert
Nat -> Sorted -> Sorted

refinement> :type merge
Sorted -> Sorted -> Sorted
```

## Tips and Tricks

### 1. Understanding Subtyping

Remember: More specific is subtype of less specific.

```
refinement> :subtype {x:Nat|x>10} <: {x:Nat|x>5}
true -- Every value > 10 is also > 5

refinement> :subtype {x:Nat|x==7} <: {x:Nat|x>0}
true -- 7 is positive

refinement> :subtype {x:Nat|true} <: Nat
true -- Trivial refinement is same as base type
```

### 2. Debugging Type Errors

Use `:check` to verify predicates:

```
refinement> :check 5 > 0
Valid

refinement> :check 0 > 0
Invalid

refinement> :check x > 0
Unknown (depends on x)
```

### 3. Path Sensitivity

Use `:path` to see refinements:

```
refinement> :path λx. if x > 0 then pred x else 0
Then branch: x : {n:Nat|n>0}  -- Safe to use pred!
Else branch: x : {n:Nat|n<=0} -- x is 0 for Nat
```

### 4. Building Complex Refinements

Start simple and refine:

```
refinement> :let V1 = Nat
refinement> :let V2 = {n:Nat | n > 0}
refinement> :let V3 = {n:Nat | n > 0 && n < 100}
refinement> :let V4 = {n:Nat | n > 0 && n < 100 && n % 2 == 0}
```

### 5. Testing Subtyping

```
refinement> :subtype V4 <: V3
true

refinement> :subtype V3 <: V2
true

refinement> :subtype V2 <: V1
true

refinement> :subtype V1 <: V2
false -- Not all Nat are positive
```

## Common Patterns

### Non-Null Pattern

```
refinement> :let NonNull = λa. {x: Maybe a | x != Nothing}
refinement> :type fromJust
NonNull a -> a
```

### Range Pattern

```
refinement> :let Range = λlo. λhi. {n:Nat | n >= lo && n <= hi}
refinement> :let Byte = Range 0 255
refinement> :let Ascii = Range 0 127
```

### Invariant Pattern

```
refinement> :let Sorted = {xs:[Nat] | isSorted xs}
refinement> :let Unique = {xs:[Nat] | hasNoDups xs}
refinement> :let SortedUnique = {xs:[Nat] | isSorted xs && hasNoDups xs}
```

## Exercises

Try these in the REPL:

### Exercise 1: Basic Refinements
Define types for:
- Even numbers
- Numbers less than 1000
- Booleans that are false

### Exercise 2: Subtyping
Check these subtyping relationships:
- Is `{x:Nat|x>100}` a subtype of `{x:Nat|x>50}`?
- Is `{x:Nat|x==42}` a subtype of `{x:Nat|x>0}`?

### Exercise 3: Safe Operations
Write safe versions of:
- `div` (division by non-zero)
- `head` (head of non-empty list)
- `pred` (predecessor of positive number)

### Exercise 4: Path Sensitivity
Write a function that:
- Takes a Nat
- Returns its predecessor if positive, else 0
- Verify it type checks without annotations in branches

### Exercise 5: Dependent Types
Write types for:
- `replicate n x` - List of length n containing x
- `take n xs` - First n elements (requires list of length >= n)
- `split n xs` - Split list at position n

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected '|'`

**Solution**: Ensure proper refinement syntax: `{x: T | pred}`

### Subtyping Failures

**Problem**: Expected subtyping doesn't work

**Debug**:
```
refinement> :implies <your-pred>, <expected-pred>
refinement> :check <your-pred>
```

### Type Checker Too Conservative

**Problem**: Valid program rejected

**Cause**: Our simple predicate checker can't prove all implications

**Solution**: Use simpler predicates or add intermediate assertions

### Path Conditions Not Working

**Problem**: Expected refinement in branch doesn't appear

**Solution**: Ensure condition is syntactically a comparison:
```
Good: if x > 0 then ...
Bad:  let b = x > 0 in if b then ...  -- b is not x > 0 syntactically
```

## Further Reading

- [Chapter 11 README](README.md) - Complete theory and formal rules
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step tutorial
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- LiquidHaskell documentation - Real-world refinement types
- F* tutorial - Dependent types with refinements

## Next Steps

After mastering the refinement types REPL:
- Chapter 12: Effect Systems (track computational effects)
- LiquidHaskell: Apply refinements to Haskell code
- F*: Dependent types with SMT-backed verification

Have fun preventing bugs with types!
