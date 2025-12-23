# Chapter 11: Refinement Types - Frequently Asked Questions

## Conceptual Questions

### Q: What are refinement types?

**A:** Refinement types extend simple types with logical predicates. A refinement type `{x: T | φ(x)}` describes values of type T that satisfy predicate φ.

Examples:
- `{x: Nat | x > 0}` - positive naturals
- `{x: Nat | x < 100}` - naturals under 100
- `{x: Bool | x == true}` - only true

### Q: How are refinement types different from dependent types?

**A:** Refinement types are a restricted form of dependent types:

| Aspect | Refinement Types | Full Dependent Types |
|--------|------------------|---------------------|
| Predicates | Decidable logic (often) | Arbitrary terms |
| Type checking | Decidable with SMT | May require proofs |
| Expressiveness | Limited but practical | Fully expressive |
| Automation | High (SMT solvers) | Often manual |

Refinement types prioritize automation over expressiveness.

### Q: What's the relationship to contracts?

**A:** Refinement types are like static contracts:

**Dynamic contracts (Racket, Eiffel)**:
```
(define/contract (div n d)
  (-> integer? (and/c integer? positive?) integer?)
  (quotient n d))
-- Checked at runtime
```

**Refinement types**:
```
div : Nat -> {d: Nat | d > 0} -> Nat
-- Checked at compile time!
```

Refinements move contract checking to compile time.

### Q: Why is subtyping based on implication?

**A:** Think of types as sets of values:
- `{x: Nat | x > 10}` = {11, 12, 13, ...}
- `{x: Nat | x > 5}` = {6, 7, 8, ...}
- First is a SUBSET of second
- Subset = subtype in type theory

If φ(x) implies ψ(x), then every value satisfying φ also satisfies ψ.

### Q: What is path sensitivity?

**A:** Path sensitivity uses information from conditionals. In:
```
if x > 5 then t else e
```
- In `t`: we know `x > 5`
- In `e`: we know `x <= 5`

This allows type refinement based on control flow.

## Technical Questions

### Q: How does the type checker verify predicates?

**A:** Several approaches:

1. **Ground evaluation**: No variables? Just compute.
   ```
   5 > 0 → true
   ```

2. **Syntactic rules**: Simple patterns.
   ```
   p ⟹ p → true
   p && q ⟹ p → true
   ```

3. **SMT solvers**: Full logical reasoning.
   ```
   x > 10 ⟹ x > 5 → Query Z3 → true
   ```

Our implementation uses simple rules. Production systems use SMT solvers.

### Q: What is an SMT solver?

**A:** SMT = Satisfiability Modulo Theories. An SMT solver checks if logical formulas are satisfiable, with support for specific theories like arithmetic.

Common SMT solvers:
- Z3 (Microsoft)
- CVC5
- Yices

For linear arithmetic, they can decide most refinement queries.

### Q: Why can't refinement types express everything?

**A:** Decidability tradeoff:

- Simple predicates (linear arithmetic): Decidable
- Complex predicates (general recursion): Undecidable

Example of undecidable refinement:
```
{x: Nat | halts(program, x)}  -- Undecidable!
```

Practical systems restrict predicates to decidable theories.

### Q: How do I write good refinement annotations?

**A:** Guidelines:

1. **Start with preconditions**:
   ```
   div : Nat -> {d: Nat | d > 0} -> Nat
   ```

2. **Add postconditions when useful**:
   ```
   abs : Int -> {n: Nat | n >= 0}
   ```

3. **Use path sensitivity**:
   ```
   -- Don't annotate everything; let branches refine types
   ```

4. **Keep predicates in decidable fragment**:
   - Linear arithmetic is good
   - Avoid complex functions in predicates

### Q: What is Liquid Haskell?

**A:** LiquidHaskell adds refinement types to Haskell:

```haskell
{-@ div :: Nat -> {d:Nat | d > 0} -> Nat @-}
div n d = n `quot` d

{-@ type Pos = {v:Int | v > 0} @-}
```

Features:
- Automatic type inference using "liquid types"
- SMT-based verification (Z3)
- Works with existing Haskell code

### Q: How do refinements interact with polymorphism?

**A:** Refinements can be polymorphic:

```
id : (a: T) -> {b: T | b == a}
id x = x
```

The refinement `b == a` relates input to output.

For type variables:
```
head : forall a. {xs: List a | length xs > 0} -> a
```

The predicate `length xs > 0` works for any element type.

## Common Confusions

### Q: Is `{x: Nat | true}` different from `Nat`?

**A:** Semantically equivalent! Both include all natural numbers.

But syntactically they're different types. Most systems treat them as equal during subtyping:
```
Nat <: {x: Nat | true}
{x: Nat | true} <: Nat
```

### Q: Can I use refinements for security?

**A:** Yes! Refinement types can encode security levels:

```
type Public a = {x: a | level x == Public}
type Secret a = {x: a | level x == Secret}

-- Can only declassify through explicit channel
declassify : Secret a -> IO (Public a)
```

Research: F*, refinement types for security verification.

### Q: Why do I get "cannot prove" errors?

**A:** Common causes:

1. **Predicate too complex**:
   ```
   {x: Nat | fibonacci x == x}  -- Too complex
   ```

2. **Missing path information**:
   ```
   λx. pred x  -- No info that x > 0
   ```
   Fix: Add conditional or annotation.

3. **SMT solver limitation**:
   Some valid implications are hard to prove automatically.

### Q: What's the difference between `(x: T) -> U` and `T -> U`?

**A:** Whether x is named and available in U:

```
T -> U              -- x not named, U can't mention argument
(x: T) -> U         -- x is named, U can mention x

-- Example:
Nat -> Nat                          -- Simple
(n: Nat) -> {m: Nat | m > n}       -- Dependent (mentions n)
```

## Troubleshooting

### Q: Type checker is slow on my code.

**A:** Common causes:

1. **Complex predicates**: Simplify refinements
2. **Deep nesting**: Break into smaller functions
3. **Many annotations**: Let inference do more work

### Q: I can't express my invariant.

**A:** Options:

1. **Approximate it**: Use weaker but expressible predicate
2. **Abstract it**: Define a type alias for the concept
3. **Use ghost state**: Track invariant in auxiliary type

### Q: How do I debug refinement errors?

**A:** Steps:

1. **Read the error carefully**: What implication failed?
2. **Check subtyping direction**: More specific <: less specific
3. **Add intermediate annotations**: Narrow down the issue
4. **Try simpler predicates**: Isolate the problem
5. **Check path conditions**: Are you missing branch info?

### Q: Can refinements express "sorted list"?

**A:** Yes, but it's complex:

```
type Sorted a = {xs: List a | isSorted xs}
```

The predicate `isSorted` needs to be defined:
```
isSorted []  = true
isSorted [_] = true
isSorted (x:y:rest) = x <= y && isSorted (y:rest)
```

This requires recursive predicates, which not all systems support.

Simpler approach: Use smart constructors.
```
insert : a -> Sorted a -> Sorted a  -- Maintains invariant
```
