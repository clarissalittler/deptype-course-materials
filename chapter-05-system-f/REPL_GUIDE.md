# Chapter 5: System F - REPL User Guide

## Overview

The System F REPL introduces **explicit polymorphism** - you control when and how type abstraction happens. Unlike Hindley-Milner's automatic inference, here you explicitly abstract over types and apply types to terms. This is the foundation of modern generics in Java, C#, and Scala.

**Key Features**: Type abstraction (`Λα. t`), type application (`t [T]`), universal types (`∀α. T`)

**Power**: Encode almost any data type purely with functions!

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-05-system-f
stack build

# Run the REPL
stack exec system-f-repl
```

### Your First Polymorphic Term

```
λ> /\A. \x:A. x
  : ∀A. A → A
  Λα. λx:α. x

λ> (/\A. \x:A. x) [Nat]
  : Nat → Nat
  λx:Nat. x

λ> (/\A. \x:A. x) [Nat] zero
  : Nat
  0

λ> :help
  [Shows available commands]
```

**Note**: `/\A` is type abstraction (Λα), `[Nat]` is type application

## Features

### 1. Type Abstraction (Λα. t)

Abstract over types explicitly:

```
λ> /\A. \x:A. x
  : ∀A. A → A
  Λα. λx:α. x
  (polymorphic identity - explicit)

λ> /\A. /\B. \x:A. \y:B. x
  : ∀A. ∀B. A → B → A
  Λα. Λβ. λx:α. λy:β. x
  (polymorphic const - two type parameters)
```

**Syntax**: `/\A. term` or `Λα. term`

### 2. Type Application (t [T])

Apply types to polymorphic terms:

```
λ> :let id = /\A. \x:A. x
  id : ∀A. A → A

λ> id [Nat]
  : Nat → Nat
  λx:Nat. x

λ> id [Bool]
  : Bool → Bool
  λx:Bool. x

λ> id [Nat] zero
  : Nat
  0

λ> id [Bool] true
  : Bool
  true
```

**Syntax**: `term [Type]`

### 3. Universal Types (∀α. T)

Types can be quantified over type variables:

```
λ> :type /\A. \x:A. x
  /\A. \x:A. x : ∀A. A → A

λ> :type /\A. /\B. \f:A->B. \x:A. f x
  ... : ∀A. ∀B. (A → B) → A → B

λ> :type /\A. /\B. /\C. \f:B->C. \g:A->B. \x:A. f (g x)
  ... : ∀A. ∀B. ∀C. (B → C) → (A → B) → A → C
```

### 4. Explicit vs Implicit Types

**System F** (explicit):
```
λ> /\A. \x:A. x                    -- Must write type abstraction
λ> (/\A. \x:A. x) [Nat]            -- Must write type application
```

**Hindley-Milner** (implicit):
```
λ> \x. x                           -- Type abstraction automatic
λ> id 0                            -- Type application automatic
```

**Tradeoff**: System F is more verbose but more expressive!

### 5. Church Encodings

Encode data types using only functions and types:

#### Church Booleans in System F

```
λ> :let Bool = forall A. A -> A -> A
λ> :let true = /\A. \t:A. \f:A. t
  true : ∀A. A → A → A

λ> :let false = /\A. \t:A. \f:A. f
  false : ∀A. A → A → A

λ> :let if = /\A. \b:(forall B. B->B->B). \t:A. \f:A. b [A] t f
  if : ∀A. (∀B. B → B → B) → A → A → A

λ> if [Nat] true zero (succ zero)
  : Nat
  0
```

#### Church Numerals in System F

```
λ> :let Nat = forall A. (A -> A) -> A -> A
λ> :let zero = /\A. \f:A->A. \x:A. x
  zero : ∀A. (A → A) → A → A

λ> :let one = /\A. \f:A->A. \x:A. f x
λ> :let two = /\A. \f:A->A. \x:A. f (f x)

λ> :let succ = \n:(forall A. (A->A)->A->A).
                 /\A. \f:A->A. \x:A. f (n [A] f x)
  succ : (∀A. (A → A) → A → A) → ∀A. (A → A) → A → A
```

#### Church Pairs in System F

```
λ> :let Pair = \A:*. \B:*. forall C. (A -> B -> C) -> C

λ> :let pair = /\A. /\B. \x:A. \y:B.
                 /\C. \f:A->B->C. f x y
  pair : ∀A. ∀B. A → B → ∀C. (A → B → C) → C

λ> :let fst = /\A. /\B. \p:(forall C. (A->B->C)->C).
                p [A] (\x:A. \y:B. x)
  fst : ∀A. ∀B. (∀C. (A → B → C) → C) → A

λ> :let snd = /\A. /\B. \p:(forall C. (A->B->C)->C).
                p [B] (\x:A. \y:B. y)
  snd : ∀A. ∀B. (∀C. (A → B → C) → C) → B
```

### 6. Parametricity

Polymorphic functions are **parametric** - they work uniformly:

```
λ> :let id = /\A. \x:A. x
  -- 'id' can't inspect the type A
  -- It MUST return x unchanged
  -- This is parametricity!

λ> :let const = /\A. /\B. \x:A. \y:B. x
  -- 'const' MUST return x
  -- Can't do anything with x or y
  -- Types enforce parametric behavior!
```

**Free Theorems**: From types alone, we can derive properties!

### 7. Bidirectional Type Checking

System F uses bidirectional type checking:

- **Checking mode**: Verify a term has a given type
- **Synthesis mode**: Infer the type of a term

```
λ> :check (/\A. \x:A. x) : forall A. A -> A
  ✓ Term has the given type

λ> :synth /\A. \x:A. x
  Synthesized type: ∀A. A → A
```

### 8. Type Bindings

Bind types for convenience:

```
λ> :tlet Bool = forall A. A -> A -> A
  Bool = ∀A. A → A → A

λ> :tlet Nat = forall A. (A -> A) -> A -> A
  Nat = ∀A. (A → A) → A → A

λ> :tlet Pair = \A:*. \B:*. forall C. (A -> B -> C) -> C
  Pair = λα:*. λβ:*. ∀C. (α → β → C) → C

λ> :tbindings
Type bindings:
  Bool = ∀A. A → A → A
  Nat = ∀A. (A → A) → A → A
  Pair = λα:*. λβ:*. ∀C. (α → β → C) → C
```

### 9. Impredicativity

System F is **impredicative** - quantified types can be instantiated with quantified types!

```
λ> :let id = /\A. \x:A. x
λ> id [forall B. B -> B] id
  : ∀A. A → A
  Λα. λx:α. x

  -- Applied id to a POLYMORPHIC TYPE!
```

This is powerful but makes inference undecidable.

### 10. Step-by-Step Evaluation

Watch type application and reduction:

```
λ> :step
Step mode enabled

λ> (/\A. \x:A. x) [Nat] zero
  : Nat
  (Λα. λx:α. x) [Nat] 0
    [Press Enter]
→ (λx:Nat. x) 0
    [Press Enter]
→ 0
  (normal form)

λ> :step
λ> (/\A. /\B. \x:A. \y:B. x) [Nat] [Bool] zero true
  (Λα. Λβ. λx:α. λy:β. x) [Nat] [Bool] 0 true
    [Press Enter]
→ (Λβ. λx:Nat. λy:β. x) [Bool] 0 true
    [Press Enter]
→ (λx:Nat. λy:Bool. x) 0 true
    [Press Enter]
→ (λy:Bool. 0) true
    [Press Enter]
→ 0
```

## Command Reference

### Essential Commands
- `:help` - Show help and syntax reference
- `:quit` or `:q` - Exit the REPL
- `:type <term>` - Show the type of a term
- `:let <name> = <term>` - Bind a term
- `:tlet <name> = <type>` - Bind a type

### Environment Commands
- `:bindings` or `:env` - Show term bindings
- `:tbindings` or `:tenv` - Show type bindings
- `:reset` - Clear all bindings
- `:clear` - Clear the screen

### Type Checking Commands
- `:check <term> : <type>` - Check if term has type
- `:synth <term>` - Synthesize type for term

### Evaluation Commands
- `:step` - Enable step-by-step evaluation
- `:nostep` - Disable step mode
- `:trace` - Show all evaluation steps
- `:notrace` - Hide evaluation steps

### Information Commands
- `:examples` - Show comprehensive System F examples
- `:syntax` - Show syntax reference
- `:church` - Show Church encoding examples

## Guided Exploration

### Exercise 1: Type Abstraction Basics (10 minutes)

Practice explicit type abstraction:

```
λ> /\A. \x:A. x
λ> :type /\A. \x:A. x

λ> /\A. /\B. \x:A. \y:B. x
λ> :type /\A. /\B. \x:A. \y:B. x

λ> /\A. /\B. /\C. \f:B->C. \g:A->B. \x:A. f (g x)
λ> :type /\A. /\B. /\C. \f:B->C. \g:A->B. \x:A. f (g x)
```

**Question**: Why do we need to write `/\A` explicitly?

### Exercise 2: Type Application (10 minutes)

Practice applying types:

```
λ> :let id = /\A. \x:A. x
λ> id [Nat]
λ> id [Bool]
λ> id [Nat->Nat]
λ> id [forall A. A->A]

λ> :let const = /\A. /\B. \x:A. \y:B. x
λ> const [Nat] [Bool]
λ> const [Nat] [Bool] zero true
```

**Challenge**: Apply `const` to polymorphic types.

### Exercise 3: Church Booleans (20 minutes)

Implement boolean logic:

```
λ> :tlet CBool = forall A. A -> A -> A
λ> :let true = /\A. \t:A. \f:A. t
λ> :let false = /\A. \t:A. \f:A. f

λ> :let and = \b1:CBool. \b2:CBool.
                /\A. \t:A. \f:A. b1 [A] (b2 [A] t f) f
λ> :type and

λ> and true true
λ> and true false
λ> and false true

λ> :let or = \b1:CBool. \b2:CBool.
               /\A. \t:A. \f:A. b1 [A] t (b2 [A] t f)
λ> or true false
```

**Challenge**: Implement `not` and `xor`.

### Exercise 4: Church Numerals (25 minutes)

Implement arithmetic:

```
λ> :tlet CNat = forall A. (A -> A) -> A -> A
λ> :let zero = /\A. \f:A->A. \x:A. x
λ> :let one = /\A. \f:A->A. \x:A. f x
λ> :let two = /\A. \f:A->A. \x:A. f (f x)

λ> :let succ = \n:CNat. /\A. \f:A->A. \x:A. f (n [A] f x)
λ> :type succ
λ> succ one
λ> succ (succ one)

λ> :let add = \m:CNat. \n:CNat.
                /\A. \f:A->A. \x:A. m [A] f (n [A] f x)
λ> :type add
λ> add one two

λ> :let mult = \m:CNat. \n:CNat.
                 /\A. \f:A->A. m [A] (n [A] f)
λ> :type mult
λ> mult two two
```

**Challenge**: Implement `pred` (predecessor).

### Exercise 5: Church Pairs (20 minutes)

Implement pairs:

```
λ> :tlet CPair = \A:*. \B:*. forall C. (A -> B -> C) -> C

λ> :let pair = /\A. /\B. \x:A. \y:B.
                 /\C. \f:A->B->C. f x y
λ> :type pair

λ> :let fst = /\A. /\B. \p:CPair A B. p [A] (\x:A. \y:B. x)
λ> :type fst

λ> :let snd = /\A. /\B. \p:CPair A B. p [B] (\x:A. \y:B. y)
λ> :type snd

λ> :let myPair = pair [Nat] [CBool] zero true
λ> fst [Nat] [CBool] myPair
λ> snd [Nat] [CBool] myPair
```

**Challenge**: Implement `swap` for pairs.

### Exercise 6: Parametricity (15 minutes)

Explore free theorems:

```
λ> :let id = /\A. \x:A. x
  -- By type alone: id MUST return its argument unchanged
  -- Cannot do anything else!

λ> :let const = /\A. /\B. \x:A. \y:B. x
  -- By type alone: const MUST return its first argument
  -- Cannot inspect or modify x or y!

λ> :let compose = /\A. /\B. /\C. \f:B->C. \g:A->B. \x:A. f (g x)
  -- By type alone: compose MUST apply g then f
  -- No other behavior possible!
```

**Question**: What can a function of type `∀A. ∀B. A → B` do?
**Answer**: Nothing! No such function exists (except non-terminating ones).

### Exercise 7: Impredicativity (15 minutes)

Use polymorphic types as arguments:

```
λ> :let id = /\A. \x:A. x

# Apply id to itself (polymorphic type)
λ> id [forall B. B -> B] id
  : ∀A. A → A

# Create list of polymorphic functions
λ> :tlet IdList = forall C. ((forall A. A->A) -> C -> C) -> C -> C
λ> :let idList = /\C. \cons:(forall A. A->A)->C->C. \nil:C.
                   cons id (cons id nil)
λ> :type idList
```

**Key Insight**: Quantified types can contain quantified types!

## Common REPL Workflows

### Workflow 1: Implementing Church Encodings
1. Define the type (`:tlet Type = ...`)
2. Implement constructors
3. Implement eliminators/observers
4. Test with concrete examples
5. Verify parametricity

### Workflow 2: Type-Driven Development
1. Start with the type signature
2. Let the types guide the implementation
3. Use type holes if available
4. Check with `:check`
5. Test the term

### Workflow 3: Understanding Parametricity
1. Write a polymorphic type
2. Try to implement it multiple ways
3. Realize there's only ONE way
4. Understand the free theorem

## Tips and Tricks

### Tip 1: Type Application is Explicit
```
λ> id [Nat] zero       ✓ Must apply type explicitly
λ> id zero             ✗ Type application required!
```

### Tip 2: Use :tlet for Complex Types
```
λ> :tlet Bool = forall A. A -> A -> A
λ> :let true = /\A. \t:A. \f:A. t : Bool
```

### Tip 3: Count Type Applications
```
∀A. ∀B. A → B        needs 2 type applications: [T1] [T2]
∀A. A → A            needs 1 type application: [T]
```

### Tip 4: Parentheses for Clarity
```
λ> (/\A. \x:A. x) [Nat] zero    ✓ Clear
λ> /\A. \x:A. x [Nat] zero      ✗ Confusing!
```

### Tip 5: Church Encodings Pattern
```
Type     = forall Result. (constructors) -> Result
Value    = /\Result. \args. (use constructors)
Eliminator = \value. value [DesiredType] (handlers)
```

## Troubleshooting

### Problem: "Type application expected"
**Cause**: Forgot to apply type to polymorphic term
**Solution**: Add `[Type]`
```
λ> id zero          ✗
λ> id [Nat] zero    ✓
```

### Problem: "Cannot infer type"
**Cause**: System F type inference is undecidable
**Solution**: Add type annotations
```
λ> \x. x            ✗ Cannot infer
λ> /\A. \x:A. x     ✓ Explicit abstraction
```

### Problem: "Type mismatch in application"
**Cause**: Wrong type applied
**Solution**: Check expected type
```
λ> id [Bool] zero   ✗ zero : Nat, not Bool
λ> id [Nat] zero    ✓
```

### Problem: "Ill-kinded type"
**Cause**: Type constructor used incorrectly
**Solution**: Check kind (covered in Chapter 6)

## Syntax Reference

### Types
```
A, B, C, ...        -- Type variables
Nat, Bool, ...      -- Base types
T1 -> T2            -- Function types
forall A. T         -- Universal quantification (∀α. τ)
```

### Terms
```
x, y, z, ...           -- Variables
\x:T. t                -- Lambda abstraction (typed)
t1 t2                  -- Application
/\A. t                 -- Type abstraction (Λα. t)
t [T]                  -- Type application
```

### REPL-specific
```
:tlet Name = Type      -- Bind type name
:let name = term       -- Bind term name
:type term             -- Show type
:check term : type     -- Check type
```

## Comparison with Previous Chapters

| Feature | Chapter 4 (HM) | Chapter 5 (System F) |
|---------|----------------|----------------------|
| Type abstraction | Implicit | Explicit (`/\A`) |
| Type application | Automatic | Explicit (`[T]`) |
| Type inference | Complete | Undecidable |
| Expressiveness | Limited | Very high |
| Polymorphism | Let-polymorphism | Full polymorphism |
| Impredicativity | No | Yes |

## Connection to Real Languages

System F relates to:

- **Java Generics**: `<T>` corresponds to `/\A`
- **C# Generics**: Similar to Java
- **Scala**: Full System F support
- **Haskell**: Under the hood (GHC Core)
- **Rust**: Generic types `<T>`

## Key Theoretical Properties

1. **Strong Normalization**: All well-typed terms terminate
2. **Parametricity**: Types enforce uniform behavior
3. **Undecidable Inference**: Cannot automatically infer types
4. **Expressive**: Can encode all ADTs as functions

## Next Steps

After mastering this REPL:
1. Complete exercises in `exercises/EXERCISES.md`
2. Work through `TUTORIAL.md` for deeper understanding
3. Take `QUIZ.md` to test your knowledge
4. Review `COMMON_MISTAKES.md` for pitfalls
5. Move to Chapter 6 for higher-kinded types (System F-omega)

## Quick Reference Card

```
# Building
stack build && stack exec system-f-repl

# Type Abstraction/Application
/\A. term              -- Type abstraction (Λα)
term [Type]            -- Type application

# Universal Types
forall A. T            -- ∀α. τ

# Church Encodings
:tlet Bool = forall A. A -> A -> A
:let true = /\A. \t:A. \f:A. t
:let false = /\A. \t:A. \f:A. f

# Type Bindings
:tlet Name = Type      -- Save type definition
:tbindings             -- Show all type bindings

# Key Insight
Polymorphism is EXPLICIT, not inferred!
```

Happy type abstracting! 🎭
