# Chapter 11: Refinement Types - Exercises

## Exercise 1: Understanding Refinements

For each refinement type, describe what values it contains:

1. `{x: Nat | x == 0}`
2. `{x: Nat | x > 0}`
3. `{x: Nat | x >= 0 && x < 10}`
4. `{x: Bool | x == true}`
5. `{x: Nat | x > 5 && x < 3}`

## Exercise 2: Subtyping Relationships

Determine if the first type is a subtype of the second. Explain why or why not.

1. `{x: Nat | x > 5}` <: `{x: Nat | x > 0}`
2. `{x: Nat | x > 0}` <: `{x: Nat | x > 5}`
3. `{x: Nat | x > 0}` <: `Nat`
4. `Nat` <: `{x: Nat | x >= 0}`
5. `{x: Nat | x == 0}` <: `{x: Nat | x <= 0}`

## Exercise 3: Type Checking

Which of these terms are well-typed? If ill-typed, explain why.

```
1. λx : {n: Nat | n > 0}. pred x

2. λx : Nat. (x : {n: Nat | n >= 0})

3. λx : {n: Nat | n > 0}.
     if iszero x then 0 else x

4. let x = 5 in (x : {n: Nat | n > 0})
```

## Exercise 4: Path Sensitivity

Explain how path sensitivity helps type check this term:

```
λx : Nat.
  if iszero x
  then (0 : {n: Nat | n == 0})
  else (x : {n: Nat | n > 0})
```

What predicates are available in each branch?

## Exercise 5: Implement Positive Division

Design types for a safe division function that:
- Takes a numerator (any natural)
- Takes a denominator (positive natural)
- Returns a natural

```
div : (Nat, {d: Nat | d > 0}) -> Nat
```

How does the refinement prevent division by zero?

## Exercise 6: Array Bounds Checking

Design types for array operations that prevent out-of-bounds access:

```
type Array n a = {a: Array a | length a == n}

get : (i: Nat, a: Array n a, {proof: i < n}) -> a
set : (i: Nat, a: Array n a, {proof: i < n}, v: a) -> Array n a
```

How do refinements help catch bounds errors at compile time?

## Exercise 7: Extend the Predicate Language

Add multiplication to the predicate language:

1. Extend `PArith` to support `PAMul PArith PArith` (not just scalar)
2. Update substitution
3. Update the validity checker (note: this may make validity undecidable!)

What are the trade-offs of adding full multiplication?

## Exercise 8: Implement Predicate Simplification

Write a function that simplifies predicates:

```haskell
simplify :: Pred -> Pred
```

Handle at least:
- `PTrue && p` → `p`
- `PFalse && p` → `PFalse`
- `PTrue || p` → `PTrue`
- `PFalse || p` → `p`
- `!!p` → `p`
- `x == x` → `PTrue`

## Exercise 9: Add Lists with Length Refinements

Extend the type system to support lists with length information:

```
List n a = {l: List a | length l == n}

nil  : List 0 a
cons : a -> List n a -> List (n+1) a
head : List (n+1) a -> a
tail : List (n+1) a -> List n a
```

Implement:
1. The syntax (types and terms)
2. Type checking rules
3. Evaluation

## Exercise 10: Bidirectional Type Checking

Refactor the type checker to use bidirectional type checking:

```haskell
check :: Context -> Term -> Type -> Either TypeError ()
infer :: Context -> Term -> Either TypeError Type
```

Key rules:
- Lambda is checked (direction: down)
- Application, variables are inferred (direction: up)
- Ascription switches from checking to inferring

## Challenge Exercises

### Challenge 1: SMT Integration

Integrate an SMT solver for predicate validity:

1. Convert predicates to SMT-LIB format
2. Call an external solver (e.g., Z3)
3. Parse the result

This allows handling more complex predicates that our simple checker can't.

### Challenge 2: Liquid Types

Implement Liquid Types (Refinement Type Inference):

1. Generate template refinements with unknown predicates
2. Collect constraints from type checking
3. Solve constraints to find valid predicates

Key insight: Templates are drawn from a finite set of predicates derived from the program.

### Challenge 3: Dependent Pattern Matching

Add pattern matching that refines types:

```
match x with
| 0 => ...      -- In this branch: x : {n: Nat | n == 0}
| S n => ...    -- In this branch: x : {n: Nat | n > 0}, n : Nat
```

The pattern match must cover all cases and refine appropriately.

### Challenge 4: Refinement Type Polymorphism

Add polymorphism over refinements:

```
∀p: Nat → Prop. ({x: Nat | p x} → {y: Nat | p y})
```

This allows abstracting over the refinement predicate.

## References

- Rondon, Kawaguchi, Jhala, "Liquid Types" (PLDI 2008)
- Vazou et al., "Refinement Types for Haskell" (ICFP 2014)
- Xi, Pfenning, "Dependent Types in Practical Programming" (POPL 1999)
- Knowles, Flanagan, "Hybrid Type Checking" (POPL 2006)
- Dunfield, Pfenning, "Tridirectional Typechecking" (POPL 2004)
