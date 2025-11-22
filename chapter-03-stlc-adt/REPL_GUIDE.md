# Chapter 3: STLC with ADTs - REPL User Guide

## Overview

The STLC with ADTs REPL extends Chapter 2's simply typed lambda calculus with **Algebraic Data Types** - structured data types including products (pairs/tuples), sums (Either), and the unit type. This is where type systems start to feel like real programming languages!

**New Features**: Pattern matching, sum types, product types, records, variants

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-03-stlc-adt
stack build

# Run the REPL
stack exec stlc-adt-repl
```

### Your First ADT

```
λ> pair true zero
  : Bool * Nat
  (true, 0)

λ> fst (pair true zero)
  : Bool
  true

λ> inl true : Bool + Nat
  : Bool + Nat
  inl true

λ> :help
  [Shows available commands]
```

## Features

### 1. Product Types (Pairs)

Create and use pairs:

```
λ> pair true zero
  : Bool * Nat
  (true, 0)

λ> pair (succ zero) (succ (succ zero))
  : Nat * Nat
  (1, 2)

λ> :let myPair = pair false (succ zero)
  myPair : Bool * Nat
  myPair = (false, 1)
```

Access pair components:

```
λ> fst (pair true zero)
  : Bool
  true

λ> snd (pair true zero)
  : Nat
  0

λ> :let swap = \p:Bool*Nat. pair (snd p) (fst p)
  swap : Bool * Nat -> Nat * Bool
```

### 2. Sum Types (Either)

Create left and right values:

```
λ> inl true : Bool + Nat
  : Bool + Nat
  inl true

λ> inr zero : Bool + Nat
  : Bool + Nat
  inr 0

λ> inl (succ zero) : Nat + Bool
  : Nat + Bool
  inl 1
```

**Note**: You must provide type annotations for sum types!

### 3. Pattern Matching with case

Pattern match on sum types:

```
λ> case (inl true : Bool + Nat) of
     inl x => x
   | inr y => false
  : Bool
  true

λ> case (inr zero : Bool + Nat) of
     inl x => x
   | inr y => false
  : Bool
  false

λ> :let isLeft = \x:Bool+Nat.
                   case x of
                     inl b => true
                   | inr n => false
  isLeft : (Bool + Nat) -> Bool
```

### 4. Unit Type

The unit type has exactly one value:

```
λ> unit
  : Unit
  ()

λ> :type unit
  unit : Unit

λ> :let ignoreArg = \x:Nat. unit
  ignoreArg : Nat -> Unit
```

### 5. Nested ADTs

Combine products and sums:

```
λ> pair (inl true : Bool + Nat) (inr zero : Bool + Nat)
  : (Bool + Nat) * (Bool + Nat)
  (inl true, inr 0)

λ> inl (pair true zero) : (Bool * Nat) + (Nat * Bool)
  : (Bool * Nat) + (Nat * Bool)
  inl (true, 0)
```

### 6. Type Annotations for Clarity

While product types can often be inferred, sum types require annotations:

```
# Products - inference works
λ> pair true zero
  : Bool * Nat

# Sums - annotation required
λ> inl true : Bool + Nat
  : Bool + Nat

λ> inr zero : Bool + Nat
  : Bool + Nat
```

### 7. Named Bindings with ADTs

```
λ> :let makeResult = \success:Bool. \value:Nat.
                       if success
                       then inl value : Nat + Bool
                       else inr false : Nat + Bool
  makeResult : Bool -> Nat -> (Nat + Bool)

λ> makeResult true (succ zero)
  : Nat + Bool
  inl 1

λ> makeResult false zero
  : Nat + Bool
  inr false
```

### 8. Higher-Order Functions with ADTs

```
λ> :let mapPair = \f:Nat->Nat. \p:Nat*Nat.
                    pair (f (fst p)) (f (snd p))
  mapPair : (Nat -> Nat) -> Nat * Nat -> Nat * Nat

λ> mapPair (\x:Nat. succ x) (pair zero (succ zero))
  : Nat * Nat
  (1, 2)
```

### 9. Step-by-Step Evaluation with ADTs

Watch ADT operations evaluate:

```
λ> :step
Step mode enabled

λ> fst (pair (succ zero) (succ (succ zero)))
  : Nat
  fst (pair (succ 0) (succ (succ 0)))
    [Press Enter to step]
→ fst (pair 1 (succ (succ 0)))
    [Press Enter to step]
→ fst (pair 1 2)
    [Press Enter to step]
→ 1
  (normal form)
```

Pattern matching evaluation:

```
λ> case (inl (succ zero) : Nat + Bool) of
     inl x => succ x
   | inr b => zero
  : Nat
  case (inl (succ 0) : Nat + Bool) of ...
    [Press Enter to step]
→ case (inl 1 : Nat + Bool) of ...
    [Press Enter to step]
→ succ 1
    [Press Enter to step]
→ 2
```

### 10. Type Query for Complex Types

```
λ> :type \x:Bool*Nat. \y:Nat*Bool. pair (fst x) (snd y)
  : (Bool * Nat) -> (Nat * Bool) -> Bool * Bool

λ> :type \x:Bool+Nat. case x of inl b => b | inr n => false
  : (Bool + Nat) -> Bool

λ> :type \f:Nat->Nat. \p:Nat*Nat. pair (f (fst p)) (f (snd p))
  : (Nat -> Nat) -> Nat * Nat -> Nat * Nat
```

## Command Reference

### Essential Commands
- `:help` - Show help and syntax reference
- `:quit` or `:q` - Exit the REPL
- `:type <term>` - Show the type of a term
- `:let <name> = <term>` - Bind a term to a name

### Environment Commands
- `:bindings` or `:env` - Show all current bindings
- `:reset` - Clear all bindings
- `:clear` - Clear the screen

### Evaluation Commands
- `:step` - Enable step-by-step evaluation mode
- `:nostep` - Disable step mode
- `:trace` - Show all evaluation steps
- `:notrace` - Hide evaluation steps

### Type Checking Commands
- `:check` - Enable type checking (default)
- `:nocheck` - Disable type checking (unsafe!)

### Information Commands
- `:examples` - Show comprehensive ADT examples
- `:syntax` - Show syntax reference including ADT syntax

## Guided Exploration

### Exercise 1: Product Types (10 minutes)

Explore pairs:

```
λ> pair true false
λ> :type pair true false

λ> fst (pair true false)
λ> snd (pair true false)

λ> pair (pair true false) zero
λ> :type pair (pair true false) zero

λ> :let swap = \p:Bool*Nat. pair (snd p) (fst p)
λ> swap (pair true zero)
```

**Challenge**: Write a function to swap both components of a nested pair.

### Exercise 2: Sum Types (10 minutes)

Explore Either:

```
λ> inl true : Bool + Nat
λ> inr zero : Bool + Nat

λ> :let maybeNat = inr (succ zero) : Bool + Nat
λ> case maybeNat of inl b => b | inr n => false

λ> :let getOrFalse = \x:Bool+Nat.
                      case x of
                        inl b => b
                      | inr n => false
λ> getOrFalse (inl true : Bool + Nat)
λ> getOrFalse (inr zero : Bool + Nat)
```

**Challenge**: Write `mapLeft` that applies a function to the left value if present.

### Exercise 3: Optional Values (15 minutes)

Implement Maybe/Option using sum types:

```
λ> :let none = inr unit : Nat + Unit
λ> :let some = \x:Nat. inl x : Nat + Unit

λ> some (succ zero)
λ> none

λ> :let getOrDefault = \opt:Nat+Unit. \default:Nat.
                         case opt of
                           inl x => x
                         | inr u => default
λ> getOrDefault (some (succ zero)) zero
λ> getOrDefault none (succ (succ zero))
```

**Challenge**: Implement `mapOption` that applies a function to a `some` value.

### Exercise 4: Either for Error Handling (15 minutes)

Use Either for success/failure:

```
λ> :let success = \x:Nat. inl x : Nat + Bool
λ> :let failure = \msg:Bool. inr msg : Nat + Bool

λ> :let divide = \x:Nat. \y:Nat.
                   if iszero y
                   then failure false  -- Error: division by zero
                   else success x      -- Simplified result

λ> divide (succ zero) (succ zero)
λ> divide (succ zero) zero
```

**Challenge**: Write a function that chains two operations that can fail.

### Exercise 5: Tuples with Multiple Components (10 minutes)

Build larger tuples using nested pairs:

```
λ> :let triple = \x:Bool. \y:Nat. \z:Bool.
                   pair x (pair y z)
  triple : Bool -> Nat -> Bool -> Bool * (Nat * Bool)

λ> triple true zero false

λ> :let first3 = \t:Bool*(Nat*Bool). fst t
λ> :let second3 = \t:Bool*(Nat*Bool). fst (snd t)
λ> :let third3 = \t:Bool*(Nat*Bool). snd (snd t)

λ> first3 (triple true (succ zero) false)
λ> second3 (triple true (succ zero) false)
λ> third3 (triple true (succ zero) false)
```

**Challenge**: Create a 4-tuple and accessor functions.

### Exercise 6: Pattern Matching Mastery (15 minutes)

Complex pattern matching:

```
λ> :let processPair = \p:Bool*Nat.
                        if fst p
                        then succ (snd p)
                        else pred (snd p)
λ> processPair (pair true (succ zero))
λ> processPair (pair false (succ zero))

λ> :let processEither = \x:(Bool*Nat)+(Nat*Bool).
                          case x of
                            inl p => fst p
                          | inr p => false
λ> processEither (inl (pair true zero) : (Bool*Nat)+(Nat*Bool))
λ> processEither (inr (pair zero true) : (Bool*Nat)+(Nat*Bool))
```

**Challenge**: Write a function that handles nested Either values.

## Common REPL Workflows

### Workflow 1: Modeling Data
1. Identify what data you need to represent
2. Choose the right ADT (product for "and", sum for "or")
3. Define type synonyms mentally (e.g., `Maybe Nat = Nat + Unit`)
4. Build constructor functions with `:let`
5. Write accessor/processor functions

### Workflow 2: Pattern Matching
1. Create a sum type value
2. Use `case` to destructure it
3. Use `:step` to see which branch is taken
4. Ensure all cases are handled
5. Test with different constructors

### Workflow 3: Building Complex Types
1. Start with simple types (Bool, Nat)
2. Combine with products for records
3. Combine with sums for variants
4. Nest as needed
5. Use `:type` frequently to verify

## Tips and Tricks

### Tip 1: Type Annotations for Sums
Always annotate sum types to avoid ambiguity:
```
λ> inl true : Bool + Nat      ✓ Clear
λ> inl true                    ✗ Ambiguous! What's the right type?
```

### Tip 2: Use Meaningful Names
```
λ> :let success = \x:Nat. inl x : Nat + Bool
λ> :let failure = \msg:Bool. inr msg : Nat + Bool
```
Much clearer than raw `inl`/`inr`!

### Tip 3: Think in Terms of "And" and "Or"
- Product (`*`): "I need Bool AND Nat" → `Bool * Nat`
- Sum (`+`): "I have Bool OR Nat" → `Bool + Nat`

### Tip 4: Pattern Match Exhaustively
Always handle all cases:
```
λ> case x of
     inl a => ...   ✓ Handle left
   | inr b => ...   ✓ Handle right
```

### Tip 5: Build Complex Types Gradually
```
λ> :type pair              -- See what pair expects
λ> :type inl               -- See what inl expects
λ> :type case ... of ...   -- Build up the case expression
```

### Tip 6: Use Unit for "Nothing"
```
λ> :let Maybe_Nat = \x:Nat. inl x : Nat + Unit  -- Some
λ> :let None_Nat = inr unit : Nat + Unit        -- None
```

## Troubleshooting

### Problem: "Type annotation required for sum type"
**Cause**: Ambiguous sum type
**Solution**: Always annotate `inl` and `inr`:
```
λ> inl true : Bool + Nat   ✓
λ> inl true                ✗
```

### Problem: "Pattern match is not exhaustive"
**Cause**: Missing case in pattern match
**Solution**: Handle all constructors:
```
λ> case x of inl a => ...  ✗ Missing inr case
λ> case x of inl a => ... | inr b => ...  ✓
```

### Problem: "Type mismatch in branches"
**Cause**: Case branches have different types
**Solution**: Ensure all branches return the same type:
```
λ> case x of
     inl a => true      ✓ Returns Bool
   | inr b => false     ✓ Returns Bool
```

### Problem: "Cannot infer type of pair"
**Cause**: Complex nested pairs
**Solution**: Add explicit type annotations:
```
λ> :let p = pair (pair true false) zero : (Bool*Bool)*Nat
```

## Syntax Reference

### Types
```
Unit                    -- Unit type (one value)
T1 * T2                -- Product type (pairs)
T1 + T2                -- Sum type (either)
T1 -> T2               -- Function type
```

### Product Terms
```
unit                   -- Unit value: ()
pair <t1> <t2>         -- Create pair
fst <term>             -- First component
snd <term>             -- Second component
```

### Sum Terms
```
inl <term> : T1 + T2   -- Left injection (must annotate!)
inr <term> : T1 + T2   -- Right injection (must annotate!)

case <term> of         -- Pattern match
  inl x => <term1>
| inr y => <term2>
```

## Comparison with Previous Chapters

| Feature | Chapter 2 | Chapter 3 |
|---------|-----------|-----------|
| Data structures | Only base types | Products, sums, unit |
| Pattern matching | No | Yes (case expressions) |
| Error handling | Limited | Either type pattern |
| Optional values | Not possible | Sum types (`T + Unit`) |
| Tuples | Not possible | Nested products |
| Real-world use | Basic | Like Rust enums, TS unions |

## Connection to Real Languages

ADTs in this chapter correspond to:

- **Rust**: `enum` (sum types), tuples (product types)
- **TypeScript**: Union types (sum), tuples (product)
- **Haskell**: `Either`, `Maybe`, tuples, `()`
- **OCaml**: Variants, tuples, unit
- **Swift**: Enums with associated values

## Next Steps

After mastering this REPL:
1. Complete exercises in `exercises/EXERCISES.md`
2. Work through `TUTORIAL.md` for pattern matching details
3. Take `QUIZ.md` to test ADT understanding
4. Review `COMMON_MISTAKES.md` for pitfalls
5. Move to Chapter 4 for automatic type inference!

## Quick Reference Card

```
# Building
stack build && stack exec stlc-adt-repl

# Product Types
pair <t1> <t2>    -- Create pair
fst <pair>        -- Get first
snd <pair>        -- Get second

# Sum Types
inl <t> : T1+T2   -- Left value (annotate!)
inr <t> : T1+T2   -- Right value (annotate!)

case <sum> of     -- Pattern match
  inl x => ...
| inr y => ...

# Unit
unit              -- The only value of type Unit

# Type Syntax
Bool * Nat        -- Product (pair)
Bool + Nat        -- Sum (either)
Unit              -- Unit type
```

Happy pattern matching! 🎨
