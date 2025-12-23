# Chapter 15: Recursive Types - REPL User Guide

## Overview

The Recursive Types REPL provides an interactive environment for experimenting with μ types, fold/unfold operations, and recursive data structures.

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-15-recursive-types
stack build

# Run the REPL
stack exec recursive-repl
```

### Quick Start

```
recursive> mu a. Unit + a
  μa. Unit + a

recursive> fold [mu a. Nat] 5
  fold [μa. Nat] 5

recursive> :help
  [Shows available commands]
```

## Features

### 1. Recursive Type Definitions

Define recursive types using the μ operator:

```
recursive> :def NatList = mu a. Unit + (Nat × a)
Defined: NatList

recursive> :t NatList
μa. Unit + (Nat × a)

recursive> :def Tree = mu a. Nat + (a × a)
Defined: Tree

recursive> :t Tree
μa. Nat + (a × a)
```

### 2. Type Inspection

View types and their unfolded forms:

```
recursive> :t mu a. Unit + a
μa. Unit + a

recursive> :unfold-type mu a. Unit + a
Unit + (μa. Unit + a)

recursive> :t NatList
μa. Unit + (Nat × a)

recursive> :unfold-type NatList
Unit + (Nat × NatList)
```

### 3. Fold Operations

Wrap values into recursive types:

```
recursive> :def nil = fold [NatList] (inl unit)
Defined: nil

recursive> :t nil
NatList

recursive> :def cons = \n:Nat. \l:NatList.
             fold [NatList] (inr <n, l>)
Defined: cons

recursive> :t cons
Nat → NatList → NatList

recursive> cons 5 nil
fold [NatList] (inr <5, fold [NatList] (inl unit)>)
```

### 4. Unfold Operations

Unwrap recursive types for examination:

```
recursive> unfold [NatList] nil
inl unit : Unit + (Nat × NatList)

recursive> unfold [NatList] (cons 5 nil)
inr <5, fold [NatList] (inl unit)> : Unit + (Nat × NatList)

recursive> :def isEmpty = \l:NatList.
             case unfold [NatList] l of
               inl _ => true
             | inr _ => false
Defined: isEmpty

recursive> isEmpty nil
true

recursive> isEmpty (cons 1 nil)
false
```

### 5. Step-by-Step Evaluation

Enable step mode to see fold/unfold reductions:

```
recursive> :step
Step mode enabled

recursive> unfold [NatList] (fold [NatList] (inl unit))
  unfold [NatList] (fold [NatList] (inl unit))
    [Press Enter to step]
→ inl unit
  (normal form)
```

### 6. Tracing

Show all evaluation steps:

```
recursive> :trace
Evaluation trace enabled

recursive> isEmpty (cons 1 nil)
  case unfold [NatList] (fold [NatList] (inr <1, nil>)) of ...
  case inr <1, nil> of ...
  false
```

## Common Data Structures

### Lists

```
recursive> :def NatList = mu a. Unit + (Nat × a)
recursive> :def nil = fold [NatList] (inl unit)
recursive> :def cons = \n:Nat. \l:NatList.
             fold [NatList] (inr <n, l>)

# Build a list
recursive> :def list123 = cons 1 (cons 2 (cons 3 nil))

# List operations
recursive> :def isEmpty = \l:NatList.
             case unfold [NatList] l of
               inl _ => true
             | inr _ => false

recursive> :def head = \l:NatList.
             case unfold [NatList] l of
               inl _ => 0
             | inr p => fst p

recursive> :def tail = \l:NatList.
             case unfold [NatList] l of
               inl _ => nil
             | inr p => snd p

recursive> head list123
1

recursive> head (tail list123)
2
```

### Binary Trees

```
recursive> :def Tree = mu a. Nat + (a × a)
recursive> :def leaf = \n:Nat. fold [Tree] (inl n)
recursive> :def branch = \l:Tree. \r:Tree.
             fold [Tree] (inr <l, r>)

# Build a tree
#     *
#    / \
#   1   *
#      / \
#     2   3
recursive> :def tree1 = branch (leaf 1)
                               (branch (leaf 2) (leaf 3))

# Tree operations
recursive> :def isLeaf = \t:Tree.
             case unfold [Tree] t of
               inl _ => true
             | inr _ => false

recursive> isLeaf (leaf 5)
true

recursive> isLeaf tree1
false
```

### Streams (Infinite Data)

```
recursive> :def Stream = mu a. Nat × a

recursive> :def head = \s:Stream. fst (unfold [Stream] s)
recursive> :def tail = \s:Stream. snd (unfold [Stream] s)

# Note: Creating infinite streams requires general recursion
# In REPL, you can define with fix combinator or axiom

recursive> :axiom ones : Stream
Axiom: ones : Stream

recursive> :axiom ones-def : ones = fold [Stream] <1, ones>
Axiom: ones-def
```

## Advanced Examples

### Self-Application Type

```
recursive> :def SelfApp = mu a. a → Nat

recursive> :def omega = \x:SelfApp.
             (unfold [SelfApp] x) x

recursive> :t omega
SelfApp → Nat

# This enables typing of self-application!
recursive> :t fold [SelfApp] omega
SelfApp
```

### List Length

```
recursive> :def length = fix (\len. \l:NatList.
             case unfold [NatList] l of
               inl _ => 0
             | inr p => succ (len (snd p)))

recursive> length nil
0

recursive> length (cons 1 (cons 2 nil))
2
```

### Tree Sum

```
recursive> :def treeSum = fix (\sum. \t:Tree.
             case unfold [Tree] t of
               inl n => n
             | inr p => add (sum (fst p)) (sum (snd p)))

recursive> treeSum (leaf 5)
5

recursive> treeSum (branch (leaf 1) (leaf 2))
3
```

### List Append

```
recursive> :def append = fix (\app. \l1:NatList. \l2:NatList.
             case unfold [NatList] l1 of
               inl _ => l2
             | inr p => cons (fst p) (app (snd p) l2))

recursive> :def list12 = cons 1 (cons 2 nil)
recursive> :def list34 = cons 3 (cons 4 nil)
recursive> append list12 list34
cons 1 (cons 2 (cons 3 (cons 4 nil)))
```

### List Reverse

```
recursive> :def reverse = fix (\rev. \l:NatList.
             case unfold [NatList] l of
               inl _ => nil
             | inr p => append (rev (snd p))
                               (cons (fst p) nil))

recursive> reverse (cons 1 (cons 2 (cons 3 nil)))
cons 3 (cons 2 (cons 1 nil))
```

### Tree Height

```
recursive> :def height = fix (\h. \t:Tree.
             case unfold [Tree] t of
               inl _ => 0
             | inr p => succ (max (h (fst p)) (h (snd p))))

recursive> height (leaf 5)
0

recursive> height (branch (leaf 1) (branch (leaf 2) (leaf 3)))
2
```

## Command Reference

### Type Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:t expr` | `:type` | Show type of expression |
| `:unfold-type T` | `:ut` | Show unfolded form of recursive type |
| `:def name = expr` | `:d` | Define named term |
| `:typedef name = T` | `:td` | Define type alias |

### Evaluation Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:eval expr` | `:e` | Evaluate expression |
| `:step` | | Enable step-by-step evaluation |
| `:nostep` | | Disable step-by-step |
| `:trace` | | Show all evaluation steps |
| `:notrace` | | Hide evaluation steps |

### Definition Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:def name = term` | `:d` | Define named term |
| `:typedef name = T` | `:td` | Define type alias |
| `:axiom name : T` | | Assume term exists |
| `:defs` | | Show all definitions |
| `:clear` | `:c` | Clear all definitions |

### Information Commands

| Command | Short | Description |
|---------|-------|-------------|
| `:help` | `:h`, `:?` | Show help message |
| `:examples` | `:ex` | Show example terms |
| `:quit` | `:q`, `:exit` | Exit the REPL |

## Recursive Type Syntax

### Recursive Types
```
mu a. T             Recursive type binding a in T
μa. T               Unicode mu (alternative)
```

### Fold and Unfold
```
fold [T] t          Wrap t into recursive type T
unfold [T] t        Unwrap t from recursive type T
```

### Type Annotations
Type annotations are required for fold/unfold:
```
fold [NatList] (inl unit)        ✓ Correct
fold (inl unit)                   ✗ Missing annotation
```

## Tips and Tricks

### 1. Understanding Fold/Unfold

Think of fold and unfold as wrapper/unwrapper:

```
# Fold wraps
nil = fold [NatList] (inl unit)
     ^^^^             ^^^^^^^^^
     wrapper          unfolded value

# Unfold unwraps
case unfold [NatList] l of ...
     ^^^^^^
     unwrapper
```

### 2. Type Substitution

To understand what unfold gives you:

```
NatList = μa. Unit + (Nat × a)

After unfold:
  Unit + (Nat × a)  [a := NatList]
= Unit + (Nat × NatList)
```

### 3. Building Recursive Functions

Use the fix combinator for general recursion:

```
:def fix = \f. (\x. f (unfold x x))
                (fold (\x. f (unfold x x)))

:def factorial = fix (\fac. \n.
  if iszero n
    then 1
    else mult n (fac (pred n)))
```

### 4. Debugging Type Errors

Common issues:

```
# Missing fold
cons 1 nil            ✗ Type error
fold [...] (inr ...) ✓ Correct

# Missing unfold
case l of ...         ✗ Can't match on μ type
case unfold [...] l of ... ✓ Correct

# Wrong annotation
fold [Unit + (Nat × NatList)] ... ✗ Use μ type
fold [NatList] ...                ✓ Correct
```

### 5. Visualizing Structures

Draw out recursive structures:

```
# List: [1, 2, 3]
cons 1 (cons 2 (cons 3 nil))
= inr <1, inr <2, inr <3, inl unit>>>

# Tree:
#     *
#    / \
#   1   2
branch (leaf 1) (leaf 2)
= inr <inl 1, inl 2>
```

## Common Patterns

### Pattern 1: Empty Constructor
```
nil = fold [ListType] (inl unit)
```

### Pattern 2: Non-Empty Constructor
```
cons = \elem. \rest. fold [ListType] (inr <elem, rest>)
```

### Pattern 3: Examining Structure
```
check = \val.
  case unfold [Type] val of
    inl _ => ... -- base case
  | inr p => ... -- recursive case
```

### Pattern 4: Recursive Functions
```
recurse = fix (\self. \val.
  case unfold [Type] val of
    inl _ => base
  | inr p => ... self ... -- recurse
)
```

## Practice Exercises

### Exercise 1: Define Maybe Type
Create an optional value type:
```
recursive> :def Maybe = mu a. Unit + Nat
recursive> :def nothing = fold [Maybe] (inl unit)
recursive> :def just = \n:Nat. fold [Maybe] (inr n)
```

### Exercise 2: List Map
Implement map for lists:
```
recursive> :def map = \f. fix (\m. \l.
             case unfold [NatList] l of
               inl _ => nil
             | inr p => cons (f (fst p)) (m (snd p)))
```

### Exercise 3: Tree Mirror
Swap left and right subtrees:
```
recursive> :def mirror = fix (\m. \t.
             case unfold [Tree] t of
               inl n => leaf n
             | inr p => branch (m (snd p)) (m (fst p)))
```

### Exercise 4: List Filter
Keep elements satisfying predicate:
```
recursive> :def filter = \pred. fix (\f. \l.
             case unfold [NatList] l of
               inl _ => nil
             | inr p => if pred (fst p)
                         then cons (fst p) (f (snd p))
                         else f (snd p))
```

### Exercise 5: Tree Leaves
Collect all leaf values:
```
recursive> :def leaves = fix (\lv. \t.
             case unfold [Tree] t of
               inl n => cons n nil
             | inr p => append (lv (fst p)) (lv (snd p)))
```

## Troubleshooting

### Parse Errors

**Error**: `Parse error: unexpected 'mu'`

**Solution**: Ensure proper syntax: `mu a. T` with space after `mu` and before `.`

### Type Errors

**Error**: `Type mismatch: expected NatList, got Unit + (Nat × NatList)`

**Solution**: Add fold to wrap into recursive type:
```
fold [NatList] (inl unit)
```

### Missing Annotations

**Error**: `Cannot infer type for fold`

**Solution**: Always annotate fold/unfold with the recursive type:
```
fold [NatList] ...
unfold [NatList] ...
```

### Non-Termination

**Problem**: Infinite loops with recursive definitions.

**Solution**:
1. Check recursion terminates
2. Use lazy evaluation if available
3. Limit recursion depth in REPL

## Further Reading

- [Chapter 15 README](README.md) - Complete theory
- [TUTORIAL.md](TUTORIAL.md) - Step-by-step guide
- [CHEAT_SHEET.md](CHEAT_SHEET.md) - Quick reference
- Pierce's TAPL Chapter 20 - Recursive Types

## Next Steps

After mastering the recursive types REPL:
- Chapter 16: Homotopy Type Theory (HoTT)
- Explore coinductive types
- Study sized types for termination
- Learn about equi-recursive semantics

Have fun exploring recursive types!
