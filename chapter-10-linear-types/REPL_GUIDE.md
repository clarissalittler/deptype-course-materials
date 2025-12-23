# Chapter 10: Linear Types REPL User Guide

## Overview

The Linear Types REPL provides an interactive environment for experimenting with linear types, usage tracking, and resource management patterns.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-10-linear-types
stack build

# Run the REPL
stack exec linear-repl
```

### Quick Start

```
linear> \x:1 Nat. x
  \x:1 Nat. x : Nat -o Nat

linear> \x:ω Nat. (x, x)
  \x:ω Nat. (x, x) : Nat -> Nat * Nat

linear> let !x = !5 in (x, x)
  (5, 5) : Nat * Nat
```

## Features

### 1. Linear Functions

Functions with linear parameters (`:1`) must use their argument exactly once:

```
linear> \x:1 Nat. x
  \x:1 Nat. x : Nat -o Nat

linear> (\x:1 Nat. x) 5
  5 : Nat
```

### 2. Unrestricted Functions

Functions with unrestricted parameters (`:ω`) can use their argument any number of times:

```
linear> \x:ω Nat. (x, x)
  \x:ω Nat. (x, x) : Nat -> Nat * Nat

linear> \x:ω Nat. 0
  \x:ω Nat. 0 : Nat -> Nat

linear> \x:ω Nat. (x, (x, x))
  \x:ω Nat. (x, (x, x)) : Nat -> Nat * (Nat * Nat)
```

### 3. Pairs (Tensor Product)

Create pairs with linear values:

```
linear> (5, true)
  (5, true) : Nat * Bool

linear> \x:1 Nat. \y:1 Bool. (x, y)
  \x:1 Nat. \y:1 Bool. (x, y) : Nat -o Bool -o Nat * Bool
```

### 4. Pair Elimination

Destructure pairs - both components must be used:

```
linear> let (x, y) = (5, true) in (y, x)
  (true, 5) : Bool * Nat

linear> \p:1 (Nat * Bool). let (x, y) = p in (y, x)
  \p:1 (Nat * Bool). let (x, y) = p in (y, x) : (Nat * Bool) -o (Bool * Nat)
```

**Error** if components aren't used:

```
linear> let (x, y) = (5, true) in x
  Type error: Linear variable y not used
```

### 5. Bang Introduction

Wrap unrestricted values in bang (`!`):

```
linear> !5
  !5 : !Nat

linear> !(true, false)
  !(true, false) : !(Bool * Bool)

linear> \x:ω Nat. !x
  \x:ω Nat. !x : Nat -> !Nat
```

**Cannot** bang linear variables:

```
linear> \x:1 Nat. !x
  Type error: Cannot bang expression using linear variables
```

### 6. Bang Elimination

Unwrap bang values to use them unrestrictedly:

```
linear> let !x = !5 in (x, x)
  (5, 5) : Nat * Nat

linear> let !x = !5 in (x, (x, x))
  (5, (5, 5)) : Nat * (Nat * Nat)

linear> \b:1 !Nat. let !x = b in (x, x)
  \b:1 !Nat. let !x = b in (x, x) : !Nat -o Nat * Nat
```

### 7. Linear vs Unrestricted Comparison

#### Linear Parameters

```
linear> \x:1 Nat. x
  \x:1 Nat. x : Nat -o Nat         -- OK: x used once

linear> \x:1 Nat. (x, x)
  Type error: Linear variable x used more than once

linear> \x:1 Nat. 0
  Type error: Linear variable x not used
```

#### Unrestricted Parameters

```
linear> \x:ω Nat. x
  \x:ω Nat. x : Nat -> Nat         -- OK: x used once

linear> \x:ω Nat. (x, x)
  \x:ω Nat. (x, x) : Nat -> Nat * Nat    -- OK: x used twice

linear> \x:ω Nat. 0
  \x:ω Nat. 0 : Nat -> Nat         -- OK: x not used
```

### 8. Context Splitting

Linear variables must be split across subexpressions:

```
linear> \x:1 Nat. \y:1 Nat. (x, y)
  \x:1 Nat. \y:1 Bool. (x, y) : Nat -o Bool -o Nat * Bool
  -- x goes to left, y goes to right

linear> \x:1 Nat. \y:1 Nat. \z:1 Bool. ((x, y), z)
  \x:1 Nat. \y:1 Nat. \z:1 Bool. ((x, y), z) : Nat -o Nat -o Bool -o (Nat * Nat) * Bool
  -- x and y in left pair, z in right
```

**Error** if variable appears in multiple places:

```
linear> \x:1 Nat. (x, x)
  Type error: Linear variable x used in multiple subterms
```

### 9. Conditionals with Linear Values

Conditionals track usage across branches:

```
linear> \x:1 Nat. if true then x else 0
  \x:1 Nat. if true then x else 0 : Nat -o Nat
  -- x used in one branch: OK

linear> \x:1 Nat. if true then x else x
  \x:1 Nat. if true then x else x : Nat -o Nat
  -- x used in both branches, but only one executes: OK

linear> \x:ω Nat. if true then (x, x) else x
  \x:ω Nat. if true then (x, x) else x : Nat -> Nat * Nat ⊔ Nat
  -- x used differently in branches: OK (unrestricted)
```

## Command Reference

### Evaluation Commands

| Command | Description |
|---------|-------------|
| `<expr>` | Evaluate and type check an expression |
| `:type <expr>` | Show only the type (alias: `:t`) |
| `:eval <expr>` | Show only the value (alias: `:e`) |

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
    | \x:m T. t               -- Lambda with multiplicity
    | t1 t2                   -- Application
    | (t1, t2)                -- Pair
    | let (x, y) = t1 in t2   -- Pair elimination
    | !t                      -- Bang introduction
    | let !x = t1 in t2       -- Bang elimination
    | true | false            -- Booleans
    | if t1 then t2 else t3   -- Conditional
    | 0 | succ t | pred t     -- Natural numbers
    | ()                      -- Unit
```

### Types

```
T ::= Bool                    -- Boolean
    | Nat                     -- Natural number
    | ()                      -- Unit
    | T1 -o T2                -- Linear function (T1 -(1)-> T2)
    | T1 -> T2                -- Unrestricted function (T1 -(ω)-> T2)
    | T1 * T2                 -- Pair (tensor)
    | !T                      -- Bang type
```

### Multiplicities

```
m ::= 1    -- Linear (exactly once)
    | ω    -- Unrestricted (any number of times)
```

## Advanced Examples

### Example 1: Linear Swap

```
linear> let swap = \p:1 (Nat * Bool). let (x, y) = p in (y, x)
linear> :type swap
  (Nat * Bool) -o (Bool * Nat)

linear> swap (5, true)
  (true, 5) : Bool * Nat
```

### Example 2: Linear Composition

```
linear> let compose = \g:1 (Bool -o Nat). \f:1 (Nat -o Bool). \x:1 Nat. g (f x)
linear> :type compose
  (Bool -o Nat) -o (Nat -o Bool) -o Nat -o Nat
```

Each of `g`, `f`, and `x` used exactly once!

### Example 3: Bang Map

```
linear> let bangMap = \f:1 (Nat -> Bool). \b:1 !Nat. let !x = b in !(f x)
linear> :type bangMap
  (Nat -> Bool) -o !Nat -o !Bool

linear> let isZero = \x:ω Nat. iszero x
linear> bangMap isZero !5
  !false : !Bool
```

### Example 4: Duplication with Bang

```
linear> let duplicate = \b:1 !Nat. let !x = b in (x, x)
linear> :type duplicate
  !Nat -o Nat * Nat

linear> duplicate !5
  (5, 5) : Nat * Nat
```

### Example 5: Linear State Threading

```
linear> let state = \s:1 Nat. \f:1 (Nat -o Nat * Nat). f s
linear> :type state
  Nat -o (Nat -o Nat * Nat) -o Nat * Nat

linear> state 5 (\x:1 Nat. (x, succ x))
  (5, 6) : Nat * Nat
```

### Example 6: Resource Pattern (Conceptual)

Imagine file operations:

```
linear> -- Conceptual types (not executable):
-- open  : String -o Handle
-- read  : Handle -o (String * Handle)
-- close : Handle -o ()

-- Usage pattern:
let process = \path:1 String.
  let h = open path in
  let (content, h') = read h in
  let () = close h' in
  content
```

Handle is threaded through - can't forget to close!

### Example 7: Higher-Order Linear Functions

```
linear> let apply = \f:1 (Nat -o Bool). \x:1 Nat. f x
linear> :type apply
  (Nat -o Bool) -o Nat -o Bool

linear> let isZeroLin = \x:1 Nat. iszero x
linear> apply isZeroLin 0
  true : Bool
```

### Example 8: Bang Pair

```
linear> let bangPair = \a:1 !Nat. \b:1 !Bool. let !x = a in let !y = b in !(x, y)
linear> :type bangPair
  !Nat -o !Bool -o !(Nat * Bool)

linear> bangPair !5 !true
  !(5, true) : !(Nat * Bool)
```

## Common Patterns

### Pattern 1: Linear Identity

```
linear> \x:1 Nat. x
  \x:1 Nat. x : Nat -o Nat
```

### Pattern 2: Linear Const

```
linear> \x:ω Nat. \y:1 Bool. x
  \x:ω Nat. \y:1 Bool. x : Nat -> Bool -o Nat
```

Note: `x` is unrestricted (can ignore `y`), `y` is linear but discarded (so `x` must be unrestricted).

### Pattern 3: Pair Swap

```
linear> \p:1 (Nat * Bool). let (x, y) = p in (y, x)
  \p:1 (Nat * Bool). let (x, y) = p in (y, x) : (Nat * Bool) -o (Bool * Nat)
```

### Pattern 4: Bang Unwrap and Use

```
linear> \b:1 !Nat. let !x = b in (x, x)
  \b:1 !Nat. let !x = b in (x, x) : !Nat -o Nat * Nat
```

### Pattern 5: Threading Linear State

```
linear> \s:1 Nat. let s' = succ s in (s, s')
  \s:1 Nat. let s' = succ s in (s, s') : Nat -o Nat * Nat
```

## Tips and Tricks

### 1. When to Use Linear vs Unrestricted

**Use Linear (`:1`)** when:
- Modeling resources (files, memory, connections)
- Enforcing protocol adherence
- Ensuring single-use capabilities
- Preventing resource leaks

**Use Unrestricted (`:ω`)** when:
- Working with pure data
- Need to use value multiple times
- Don't care about resource tracking

### 2. Debugging "Variable Used More Than Once"

Count all uses of the variable:

```
\x:1 Nat. (x, x)
           ^  ^
           1  2  -- Used twice!
```

Solution: Make it unrestricted or redesign.

### 3. Debugging "Variable Not Used"

Check that every linear variable appears in the body:

```
\x:1 Nat. 0
 ^
 Linear but not used!
```

Solution: Actually use it or make it unrestricted.

### 4. Understanding Context Splitting

For `(t1, t2)`, each linear variable must appear in exactly one of `t1` or `t2`:

```
\x:1 Nat. \y:1 Nat. (x, y)
                     ^  ^
                     |  |
                    t1 t2

x appears only in t1 ✓
y appears only in t2 ✓
```

### 5. Bang Introduction Rules

Can only bang if the expression uses **no linear variables**:

```
!5                ✓ No variables
!(true, false)    ✓ No variables
\x:ω Nat. !x      ✓ x is unrestricted
\x:1 Nat. !x      ✗ x is linear
```

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected ':'`

**Solution**: Use proper multiplicity syntax: `:1` or `:ω`, not just `1` or `ω`.

### Linear Variable Errors

**Problem**: `Linear variable used more than once`

**Solutions**:
1. Make the variable unrestricted (`:ω`)
2. Use bang to make it unrestricted
3. Redesign to use it once

**Problem**: `Linear variable not used`

**Solutions**:
1. Make the variable unrestricted (`:ω`)
2. Actually use the variable in the body

### Bang Errors

**Problem**: `Cannot bang expression using linear variables`

**Solution**: Ensure all variables in the expression are unrestricted:

```
\x:1 Nat. !x          ✗ x is linear
\x:ω Nat. !x          ✓ x is unrestricted
```

### Context Splitting Errors

**Problem**: `Linear variable used in multiple subterms`

**Solution**: Each linear variable can only appear in one subexpression:

```
\x:1 Nat. (x, x)      ✗ x in both sides
\x:1 Nat. \y:1 Nat. (x, y)  ✓ x left, y right
```

## Exercises

Try these in the REPL to learn linear types:

### Exercise 1: Linear Basics
Write linear identity, swap, and first/second projection.

### Exercise 2: Bang Manipulation
Implement functions that wrap/unwrap bang values.

### Exercise 3: Resource Threading
Design a simple resource API with linear types.

### Exercise 4: Higher-Order Linear
Implement `apply`, `compose`, and `flip` with linear functions.

### Exercise 5: Context Splitting
Create complex terms with multiple linear variables.

## Real-World Connections

### Rust Ownership

Rust's ownership is similar to affine types (linear but allows discard):

```rust
let file = File::open("data.txt")?;
let contents = read_to_string(file)?;
// file is moved - can't use again
```

In our system:
```
let file : Handle = open "data.txt" in
let (contents, file') = read file in
close file'
```

### Session Types

Session types use linear types to enforce protocols:

```
type Session = Send Nat (Recv Bool End)
-- Must send Nat, then receive Bool, then close
```

### Safe Memory Management

```
malloc : Size -o Ptr
free   : Ptr -o ()
-- Must free exactly once!
```

## Advanced Topics

### Affine vs Linear

| System | Discard? | Duplicate? |
|--------|----------|------------|
| Linear | No | No |
| Affine | Yes | No |
| Relevant | No | Yes |
| Unrestricted | Yes | Yes |

Rust is affine (can drop, but can't duplicate).

### Quantitative Types

Generalize to resource counts:

```
x :0 T    -- Never used
x :1 T    -- Used once (linear)
x :ω T    -- Used any times (unrestricted)
x :n T    -- Used n times
```

### Linear Logic

Linear types correspond to linear logic:

```
A -o B     Linear implication
A * B      Tensor product
!A         Of course (exponential)
```

## Further Reading

- [README.md](README.md) - Complete theory and formal semantics
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step tutorial
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- [COMMON_MISTAKES.md](COMMON_MISTAKES.md) - Avoid common errors
- Girard (1987) - "Linear Logic" (foundational)
- Wadler (1990) - "Linear Types Can Change the World!"
- Bernardy et al. (2017) - "Linear Haskell"

## Next Steps

After mastering linear types:
- **Session types**: Communication protocols
- **Rust**: Practical ownership system
- **Idris 2**: Quantitative Type Theory
- **Clean**: Uniqueness types

Have fun exploring linear types! Understanding resource management in the type system opens up new ways of writing safe, efficient code.
