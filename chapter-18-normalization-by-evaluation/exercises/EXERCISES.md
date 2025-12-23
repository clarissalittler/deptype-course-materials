# Chapter 18: Normalization by Evaluation - Exercises

## Overview

These exercises deepen your understanding of NbE through implementation and exploration.

## Exercise 1: Add Pairs (Easy)

Extend NbE with dependent pairs (Sigma types):

```haskell
-- Syntax
data Term = ...
  | TSigma Name Term Term     -- Σ(x:A). B
  | TPair Term Term           -- (a, b)
  | TFst Term                 -- fst p
  | TSnd Term                 -- snd p

-- Semantic
data Val = ...
  | VSigma Name Val Closure
  | VPair Val Val

data Neutral = ...
  | NFst Neutral
  | NSnd Neutral
```

Implement:
1. `eval` cases for pairs
2. `quote` cases for pairs
3. Add test cases

## Exercise 2: Eta Expansion (Medium)

NbE naturally performs eta expansion for functions:
- A neutral `f` at type `A → B` becomes `λx. f x`

Implement eta expansion for pairs:
- A neutral `p` at type `Σ(x:A). B` should become `(fst p, snd p)`

Modify `quote` to perform eta expansion based on type information.

## Exercise 3: Call-by-Need (Medium)

The current implementation uses call-by-value. Modify it for call-by-need (lazy evaluation with memoization).

```haskell
import Data.IORef

data Thunk = Thunk (IORef ThunkState)
data ThunkState = Delayed (IO Val) | Forced Val
```

Key changes:
- Closures produce thunks instead of evaluating immediately
- Variable lookup forces thunks
- Memoize results after forcing

## Exercise 4: Universe Levels (Medium)

Replace `Type : Type` with a proper universe hierarchy:

```haskell
data Term = ...
  | TU Int        -- Type 0, Type 1, Type 2, ...

data Val = ...
  | VU Int
```

Rules:
- `Type n : Type (n+1)`
- `(x : A) → B : Type (max level(A) level(B))`

Implement level inference and checking.

## Exercise 5: Proof Irrelevance (Medium)

Add a proof-irrelevant modality:

```haskell
data Term = ...
  | TSquash Term     -- [A] - squashed type
  | TBox Term        -- box a - introduction
  | TUnbox Term      -- unbox p - elimination (only in proof-irrelevant context)
```

All terms in `[A]` are definitionally equal.

## Exercise 6: Glued Evaluation (Hard)

Implement "glued" evaluation where each value carries both:
- A syntactic representation
- A semantic value

```haskell
data Glue = Glue
  { glueTerm :: Term   -- For printing/debugging
  , glueVal  :: Val    -- For computation
  }
```

This enables better error messages and debugging.

## Exercise 7: Typed NbE (Hard)

The current NbE is untyped. Implement typed NbE where:
- Semantic values are indexed by their types
- Quotation uses type information for eta expansion

```haskell
-- Type-indexed semantic values
data Val (a :: Type) where
  VBool :: Bool -> Val 'Bool
  VFun  :: (Val a -> Val b) -> Val (a ':-> b)
```

## Exercise 8: Hereditary Substitution (Hard)

Implement hereditary substitution as an alternative to NbE:

```haskell
-- Substitute and normalize in one pass
heredSubst :: Ix -> Nf -> Nf -> Nf
```

Compare performance with NbE.

## Exercise 9: Compilation (Hard)

Compile NbE to an abstract machine:

```haskell
data Code
  = CVar Ix
  | CLam Code
  | CApp Code Code
  | CQuote Code      -- Switch to quotation mode
  | CEval Code       -- Switch to evaluation mode
```

## Exercise 10: Unification (Hard)

Implement higher-order unification for NbE values:

```haskell
unify :: Val -> Val -> Maybe Substitution
```

This is essential for type inference in dependently-typed languages.

## Challenge: Bidirectional Elaboration

Combine NbE with bidirectional type checking:
- Surface syntax without type annotations
- Elaborate to core syntax with full types
- Use NbE for type equality

## Challenge: NBE for System F

Implement NbE for System F (polymorphic lambda calculus):
- Handle type abstraction `Λα. e`
- Handle type application `e [τ]`
- Normalize types as well as terms

## Challenge: Observational Equality

Implement observational type theory where:
- Equality is defined by observation
- Use NbE to compute canonical forms
- Define equality for each type

## Theory Questions

1. Why does NbE terminate? (Hint: think about the structure of semantic values)

2. How does eta expansion interact with neutral terms?

3. What's the relationship between NbE and logical relations?

4. Why is quotation needed? Why can't we just use semantic values directly?

5. How does NbE compare to reduction-based normalization?
