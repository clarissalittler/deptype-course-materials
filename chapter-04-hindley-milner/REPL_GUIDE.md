# Chapter 4: Hindley-Milner Type Inference - REPL User Guide

## Overview

The Hindley-Milner REPL is where the magic happens: **automatic type inference**! Unlike Chapters 2-3 where you had to write type annotations everywhere, this REPL figures out types for you. This is the type system behind ML, OCaml, Haskell, and F#.

**Key Innovation**: Write `\x. x` instead of `\x:T. x` - types are inferred automatically!

**Superpower**: Polymorphic types like `∀a. a → a` (works for ANY type)

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-04-hindley-milner
stack build

# Run the REPL
stack exec hindley-milner-repl
```

### Your First Inferred Type

```
λ> \x. x
  : ∀a. a → a
  λx. x

λ> \x y. x
  : ∀a b. a → b → a
  λx. λy. x

λ> \f g x. f (g x)
  : ∀a b c. (b → c) → (a → b) → a → c
  λf. λg. λx. f (g x)

λ> :help
  [Shows available commands]
```

**Notice**: No type annotations needed! The REPL infers everything!

## Features

### 1. Automatic Type Inference

Just write terms - types are inferred:

```
λ> \x. x
  : ∀a. a → a
  (identity function - works for ANY type)

λ> \x y. x
  : ∀a b. a → b → a
  (const function - returns first arg, ignores second)

λ> \f x. f x
  : ∀a b. (a → b) → a → b
  (apply function to argument)
```

### 2. Polymorphic Types

Functions can work for multiple types:

```
λ> :let id = \x. x
  id : ∀a. a → a

λ> id 42          -- Works with numbers
  : Int
  42

λ> id true        -- Works with booleans
  : Bool
  true

λ> id (\x. x)     -- Works with functions!
  : ∀a. a → a
  λx. x
```

**Key Insight**: One function, many types!

### 3. Let-Polymorphism

Variables bound with `let` are polymorphic:

```
λ> let id = \x. x in id id
  : ∀a. a → a
  λx. x

λ> let const = \x y. x in const 1 true
  : Int
  1

λ> let compose = \f g x. f (g x) in compose
  : ∀a b c. (b → c) → (a → b) → a → c
```

**Important**: This is MORE powerful than lambda-bound variables!

### 4. Type Variables (α, β, γ)

The REPL uses type variables for unknown types:

```
λ> \x. x
  : ∀a. a → a
     ^   type variable 'a' means "any type"

λ> \x y. x
  : ∀a b. a → b → a
     ^ ^  'a' and 'b' can be different types

λ> \f. f f
  Type error! Occurs check failed
  (can't have α = α → β)
```

### 5. Type Query and Inference

See what types are inferred:

```
λ> :type \x. x
  \x. x : ∀a. a → a

λ> :type \f g x. f (g x)
  \f g x. f (g x) : ∀a b c. (b → c) → (a → b) → a → c

λ> :type let id = \x. x in id id
  let id = \x. x in id id : ∀a. a → a
```

### 6. Monomorphic Literals

Concrete values have concrete types:

```
λ> 42
  : Int
  42

λ> true
  : Bool
  true

λ> "hello"
  : String
  "hello"
```

### 7. Function Application and Instantiation

Polymorphic functions are instantiated when applied:

```
λ> :let id = \x. x
  id : ∀a. a → a

λ> id 42
  : Int         -- 'a' instantiated to Int
  42

λ> id true
  : Bool        -- 'a' instantiated to Bool
  true

λ> :let pair = \x y. (x, y)
  pair : ∀a b. a → b → (a, b)

λ> pair 1 true
  : (Int, Bool)
  (1, true)
```

### 8. Let vs Lambda: The Crucial Difference

**Let-bound variables are polymorphic**:
```
λ> let id = \x. x in (id 1, id true)
  : (Int, Bool)
  (1, true)
  ✓ Works! 'id' used at two different types
```

**Lambda-bound variables are NOT**:
```
λ> (\id. (id 1, id true)) (\x. x)
  Type error: Cannot unify Int with Bool
  ✗ Fails! 'id' must have ONE type
```

This is the **Value Restriction** - a key feature of Hindley-Milner!

### 9. Unification in Action

Watch the type inference algorithm work:

```
λ> :infer \f x. f (f x)

Initial constraints:
  f : α
  x : β
  f x : γ
  f (f x) : δ

After unification:
  f : β → γ
  f : γ → δ

Solution:
  f : β → β
  x : β
  Result: (β → β) → β → β

Final type: ∀a. (a → a) → a → a
```

### 10. Step-by-Step Evaluation (Still Works!)

Type inference + evaluation:

```
λ> :step
Step mode enabled

λ> let twice = \f x. f (f x) in twice (\x. x + 1) 0
  : Int
  let twice = ... in twice (λx. x + 1) 0
    [Press Enter to step]
→ (λf. λx. f (f x)) (λx. x + 1) 0
    [Press Enter to step]
→ (λx. (λx. x + 1) ((λx. x + 1) x)) 0
    [Press Enter to step]
→ (λx. x + 1) ((λx. x + 1) 0)
    [Press Enter to step]
→ (λx. x + 1) 1
    [Press Enter to step]
→ 2
```

## Command Reference

### Essential Commands
- `:help` - Show help and syntax reference
- `:quit` or `:q` - Exit the REPL
- `:type <term>` - Show the inferred type
- `:infer <term>` - Show detailed inference steps (if available)
- `:let <name> = <term>` - Bind a polymorphic term

### Environment Commands
- `:bindings` or `:env` - Show all current bindings with types
- `:reset` - Clear all bindings
- `:clear` - Clear the screen

### Evaluation Commands
- `:step` - Enable step-by-step evaluation
- `:nostep` - Disable step mode
- `:trace` - Show all evaluation steps
- `:notrace` - Hide evaluation steps

### Type Inference Commands
- `:showconstrs` - Show type constraints during inference
- `:showunify` - Show unification steps
- `:verbose` - Enable verbose type inference output

### Information Commands
- `:examples` - Show comprehensive HM examples
- `:syntax` - Show syntax reference (no annotations!)

## Guided Exploration

### Exercise 1: Polymorphism Discovery (10 minutes)

Explore what polymorphism means:

```
λ> :let id = \x. x
λ> :type id

λ> id 1
λ> id true
λ> id "hello"
λ> id (\y. y)

λ> :let const = \x y. x
λ> :type const
λ> const 1 "ignore"
λ> const true 42
```

**Question**: How can one function work with so many types?

### Exercise 2: Type Inference Practice (15 minutes)

Try to predict types before the REPL shows them:

```
λ> :type \x y. x         -- Predict, then check
λ> :type \f x. f x       -- Predict, then check
λ> :type \f g x. f (g x) -- Predict, then check
λ> :type \x y z. x z (y z) -- S combinator - tricky!
```

**Challenge**: Before typing `:type`, write down what you think the type is.

### Exercise 3: Let-Polymorphism (15 minutes)

Understand the difference between let and lambda:

```
# This works:
λ> let id = \x. x in (id 1, id true)

# This fails:
λ> (\id. (id 1, id true)) (\x. x)

# Why? Try to understand the error message

# More examples:
λ> let pair = \x y. (x, y) in (pair 1 2, pair true false)
λ> (\pair. (pair 1 2, pair true false)) (\x y. (x, y))
```

**Question**: Why does `let` give us more power?

### Exercise 4: Composition (15 minutes)

Build complex functions from simple ones:

```
λ> :let id = \x. x
λ> :let const = \x y. x
λ> :let compose = \f g x. f (g x)

λ> :type compose id id
λ> compose id id 42

λ> :type compose const id
λ> compose const id 1 2

λ> :let twice = \f. compose f f
λ> :type twice
λ> twice (\x. x + 1) 0
```

**Challenge**: Implement `thrice` using `compose`.

### Exercise 5: List Operations (20 minutes)

Implement polymorphic list functions:

```
λ> :let map = \f list.
                 if null list
                 then []
                 else cons (f (head list)) (map f (tail list))
λ> :type map

λ> map (\x. x + 1) [1, 2, 3]
λ> map (\x. not x) [true, false, true]

λ> :let filter = \pred list.
                   if null list
                   then []
                   else if pred (head list)
                        then cons (head list) (filter pred (tail list))
                        else filter pred (tail list)
λ> :type filter
λ> filter (\x. x > 0) [1, -2, 3, -4]
```

**Challenge**: Implement `foldl` and observe its type.

### Exercise 6: Type Errors (10 minutes)

Understand unification failures:

```
λ> \f. f f
  -- What's wrong? Why can't this type?

λ> \x. (x 1, x true)
  -- Why does this fail?

λ> let bad = \x. (x 1, x true) in bad (\y. y)
  -- This also fails - why?
```

**Key Lesson**: Some terms simply cannot be typed in Hindley-Milner!

### Exercise 7: Principal Types (10 minutes)

Every typeable term has a MOST GENERAL type:

```
λ> :type \x. x
  -- ∀a. a → a (most general)

λ> :type \x y. x
  -- ∀a b. a → b → a (most general)

λ> :type \f x. f (f x)
  -- ∀a. (a → a) → a → a (most general)
```

**Question**: Could these functions have more specific types? Why do we prefer the most general?

## Common REPL Workflows

### Workflow 1: Exploring Type Inference
1. Write a term without any type annotations
2. Use `:type` to see what the REPL infers
3. Try applying it to different argument types
4. Observe how type variables get instantiated
5. Use `:showconstrs` to see the inference process

### Workflow 2: Building Polymorphic Libraries
1. Define helper functions with `let`
2. Check their types are polymorphic
3. Compose them to build more complex functions
4. Test with various concrete types
5. Build a reusable library of bindings

### Workflow 3: Debugging Type Errors
1. Get a unification error
2. Break the term into smaller pieces
3. Use `:type` on each piece
4. Find where the types don't match
5. Check FAQ.md for common patterns

## Tips and Tricks

### Tip 1: No Annotations Needed!
```
λ> \x. x              ✓ Just works!
λ> \x:T. x            ✗ Don't need annotations
```

### Tip 2: Use Let for Reusable Polymorphic Functions
```
λ> let id = \x. x in ...    ✓ 'id' is polymorphic
λ> (\id. ...) (\x. x)       ✗ 'id' is monomorphic here
```

### Tip 3: Read Type Variables as "For Any Type"
```
∀a. a → a         means "for any type a, takes a and returns a"
∀a b. a → b → a   means "for any types a and b, takes a and b, returns a"
```

### Tip 4: Type Errors Are Your Friend
When the REPL says "Cannot unify X with Y":
- It found a contradiction
- Check where X and Y come from
- Fix the mismatch

### Tip 5: Build Complex Types Gradually
```
λ> :type \x. x
λ> :type \f x. f x
λ> :type \f. \x. f x
λ> :type \f g x. f (g x)
```
Build understanding step by step!

### Tip 6: Use :bindings to See Your Polymorphic Library
```
λ> :bindings
id : ∀a. a → a
const : ∀a b. a → b → a
compose : ∀a b c. (b → c) → (a → b) → a → c
```

## Troubleshooting

### Problem: "Cannot unify T1 with T2"
**Cause**: Type mismatch discovered during unification
**Solution**:
- Check what you're applying to what
- Use `:type` on subterms
- See FAQ.md for common patterns

### Problem: "Occurs check failed"
**Cause**: Trying to create an infinite type (α = α → β)
**Solution**:
- This term cannot be typed in HM
- Example: `\f. f f` is not typeable
- This is a fundamental limitation

### Problem: "Type too general/not instantiated"
**Cause**: Expected concrete type, got type variable
**Solution**:
- Provide concrete values
- Or specify more constraints

### Problem: "Let-bound variable used at incompatible types"
**Cause**: Even polymorphic types have limits
**Solution**:
- Check the term carefully
- See if you're using it consistently

## Syntax Reference

### Types (Inferred Automatically!)
```
Int, Bool, String, ...  -- Base types
α, β, γ, ...            -- Type variables (inferred)
T1 → T2                 -- Function types
∀a. T                   -- Polymorphic types (universal quantification)
```

### Terms (No Annotations!)
```
x, y, z, ...            -- Variables
\x. t                   -- Lambda (no type annotation!)
t1 t2                   -- Application
let x = t1 in t2        -- Let binding (polymorphic!)
if b then t1 else t2    -- Conditional
1, 2, 3, ...            -- Integer literals
true, false             -- Boolean literals
```

### Note on Lists
If your REPL supports them:
```
[]                      -- Empty list
cons x xs               -- Cons
[1, 2, 3]              -- List literal
head, tail, null       -- List operations
```

## Comparison with Previous Chapters

| Feature | Chapter 2 | Chapter 3 | Chapter 4 (HM) |
|---------|-----------|-----------|----------------|
| Type annotations | Required | Required | Not needed! |
| Polymorphism | No | No | Yes! (∀a. ...) |
| Type inference | No | No | Complete |
| Let-polymorphism | No | No | Yes |
| Principal types | N/A | N/A | Guaranteed |
| Flexibility | Low | Low | High |

## Connection to Real Languages

Hindley-Milner type inference powers:

- **Haskell**: Full HM with extensions
- **OCaml**: HM with value restriction
- **F#**: Based on HM
- **Rust**: Local type inference (similar ideas)
- **TypeScript**: Partial inference (inspired by HM)
- **Swift**: Type inference in many contexts

## Key Theoretical Properties

1. **Completeness**: If a term has a type, HM will find it
2. **Principal Types**: HM finds the MOST GENERAL type
3. **Decidability**: Type inference always terminates
4. **Soundness**: Inferred types are correct

## Next Steps

After mastering this REPL:
1. Complete exercises in `exercises/EXERCISES.md`
2. Work through `TUTORIAL.md` for Algorithm W details
3. Take `QUIZ.md` to test your understanding
4. Read `FAQ.md` for common questions
5. Review `COMMON_MISTAKES.md` for pitfalls
6. Move to Chapter 5 for explicit polymorphism (System F)

## Quick Reference Card

```
# Building
stack build && stack exec hindley-milner-repl

# Essential Commands
:help           -- Show help
:quit           -- Exit
:type <term>    -- Infer and show type
let x = <term>  -- Polymorphic binding

# No Annotations!
\x. x           -- Identity (not \x:T. x)
\f g x. f (g x) -- Compose

# Polymorphic Types
∀a. a → a                          -- Works for any type
∀a b. a → b → a                    -- Works for any two types
∀a b c. (b → c) → (a → b) → a → c  -- General composition

# Key Insight
let id = \x. x in id id    ✓ Let is polymorphic
(\id. id id) (\x. x)       ✗ Lambda is monomorphic
```

Happy inferring! 🔮
