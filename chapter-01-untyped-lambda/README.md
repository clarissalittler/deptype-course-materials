# Chapter 1: Untyped Lambda Calculus

## Overview

The untyped lambda calculus is a foundational model of computation introduced by Alonzo Church in the 1930s. Despite its simplicity—having just three syntactic forms—it is Turing-complete and serves as the theoretical basis for functional programming languages.

This chapter introduces the core concepts of lambda calculus and implements an interpreter with multiple evaluation strategies.

## Syntax

The syntax of untyped lambda calculus consists of three constructs:

```
t ::=                  (terms)
    x                  variable
    λx. t              abstraction (function)
    t t                application
```

### Examples

- **Identity function**: `λx. x`
- **Constant function**: `λx. λy. x` (returns first argument, ignores second)
- **Self-application**: `λx. x x`
- **Application**: `(λx. x) y` (applying identity to `y`)

## Mathematical Foundations

### Free and Bound Variables

A variable `x` is **bound** in term `t` if it appears within the scope of a lambda abstraction `λx`. Otherwise, it is **free**.

**Definition** (Free Variables):

```
FV(x) = {x}
FV(λx. t) = FV(t) \ {x}
FV(t₁ t₂) = FV(t₁) ∪ FV(t₂)
```

### Substitution

Substitution `[x ↦ s]t` replaces all free occurrences of `x` in `t` with `s`. To avoid **variable capture**, bound variables may need to be renamed (α-conversion).

**Definition** (Capture-Avoiding Substitution):

```
[x ↦ s]x = s
[x ↦ s]y = y                           (if x ≠ y)
[x ↦ s](λx. t) = λx. t                 (x is shadowed)
[x ↦ s](λy. t) = λy. [x ↦ s]t          (if y ≠ x and y ∉ FV(s))
[x ↦ s](λy. t) = λz. [x ↦ s][y ↦ z]t   (if y ≠ x and y ∈ FV(s), z fresh)
[x ↦ s](t₁ t₂) = ([x ↦ s]t₁) ([x ↦ s]t₂)
```

### Operational Semantics

The core reduction rule is **β-reduction**:

```
(λx. t) s → [x ↦ s]t
```

This says: applying a function `λx. t` to an argument `s` yields `t` with `x` replaced by `s`.

#### Evaluation Strategies

Different evaluation strategies determine the order in which β-reductions are performed:

**1. Normal Order** (Leftmost-Outermost)
- Always reduces the leftmost-outermost redex first
- **Strongly normalizing**: if a term has a normal form, normal order will find it
- May reduce under lambdas and may not terminate for some arguments

**2. Call-by-Name**
- Like normal order, but doesn't reduce under lambdas
- Arguments are passed unevaluated
- Used in Haskell (with optimizations like sharing)

**3. Call-by-Value**
- Reduces the leftmost-outermost redex, but only after its argument is a value
- Arguments are fully evaluated before function application
- Used in most strict languages (ML, Scheme, JavaScript)

### Small-Step Semantics

**Call-by-Value:**

```
              t₁ → t₁'
        ─────────────────               (E-App1)
        t₁ t₂ → t₁' t₂

              t₂ → t₂'
        ─────────────────               (E-App2)
        v₁ t₂ → v₁ t₂'

        (λx. t) v → [x ↦ v]t            (E-AppAbs)
```

Where `v` represents a value (lambda abstraction).

**Normal Order:**

```
              t₁ → t₁'
        ─────────────────               (E-App1)
        t₁ t₂ → t₁' t₂

        (λx. t₁) t₂ → [x ↦ t₂]t₁       (E-AppAbs)

              t₂ → t₂'
        ─────────────────               (E-App2) [only if t₁ is in normal form]
        t₁ t₂ → t₁ t₂'
```

## Church Encodings

Since lambda calculus has no built-in primitives, we can encode data structures and control flow using only functions.

### Booleans

```
true  = λt. λf. t
false = λt. λf. f
if    = λp. λt. λf. p t f
and   = λp. λq. p q false
or    = λp. λq. p true q
not   = λp. p false true
```

### Natural Numbers (Church Numerals)

A Church numeral represents `n` by applying a function `f` n times:

```
0 = λf. λx. x
1 = λf. λx. f x
2 = λf. λx. f (f x)
3 = λf. λx. f (f (f x))
...

succ = λn. λf. λx. f (n f x)
plus = λm. λn. λf. λx. m f (n f x)
mult = λm. λn. λf. m (n f)
```

### Pairs

```
pair = λx. λy. λf. f x y
fst  = λp. p (λx. λy. x)
snd  = λp. p (λx. λy. y)
```

## Fixed-Point Combinator

The Y combinator allows recursion without named functions:

```
Y = λf. (λx. f (x x)) (λx. f (x x))
```

**Property**: `Y g = g (Y g)` for any `g`

This enables defining recursive functions like factorial:

```
fact = Y (λf. λn. if (isZero n) 1 (mult n (f (pred n))))
```

**Note**: Y combinator doesn't terminate under call-by-value. For CBV, use the Z combinator:

```
Z = λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))
```

## Implementation

### Project Structure

```
chapter-01-untyped-lambda/
├── src/
│   ├── Syntax.hs      -- AST and substitution
│   ├── Eval.hs        -- Evaluation strategies
│   ├── Parser.hs      -- Parser for lambda terms
│   └── Pretty.hs      -- Pretty printer
├── test/
│   └── Spec.hs        -- Test suite
├── package.yaml       -- Haskell package configuration
└── README.md          -- This file
```

### Building and Testing

```bash
# Build the project
stack build

# Run tests
stack test

# Load in GHCi
stack ghci
```

### Usage Example

```haskell
import Syntax
import Eval
import Parser
import Pretty

-- Parse a term
let Right term = parseTerm "(\\x. x) y"

-- Evaluate it
let result = eval term

-- Pretty print
putStrLn $ pretty result  -- Output: y
```

## Key Concepts

1. **Abstraction**: Functions are first-class values
2. **Application**: The only way to compute is by function application
3. **Substitution**: The mechanism for parameter passing
4. **α-equivalence**: `λx. x` and `λy. y` are equivalent (renaming)
5. **β-reduction**: The core computation rule
6. **η-equivalence**: `λx. f x` and `f` are equivalent (if `x ∉ FV(f)`)
7. **Confluence**: Different reduction orders lead to the same result (if they terminate)
8. **Normalization**: Not all terms have a normal form (e.g., `(λx. x x) (λx. x x)`)

## Theoretical Properties

### Church-Rosser Theorem (Confluence)

If `t →* t₁` and `t →* t₂`, then there exists a term `t'` such that `t₁ →* t'` and `t₂ →* t'`.

**Consequence**: Normal forms are unique (up to α-equivalence).

### Standardization Theorem

Every terminating reduction sequence can be reordered into a standard reduction sequence (leftmost-outermost).

**Consequence**: Normal order evaluation is complete—if a normal form exists, normal order will find it.

## References

### Essential Reading

1. **Barendregt, H. P.** (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.
   - The definitive reference on lambda calculus
   - Comprehensive treatment of theory and metatheory

2. **Pierce, Benjamin C.** (2002). *Types and Programming Languages*. MIT Press.
   - Chapter 5: The Untyped Lambda Calculus
   - Excellent introduction with implementation focus
   - Available online: https://www.cis.upenn.edu/~bcpierce/tapl/

3. **Hankin, Chris** (2004). *An Introduction to Lambda Calculi for Computer Scientists*. College Publications.
   - Concise introduction
   - Good balance of theory and practice

### Additional Resources

4. **Church, Alonzo** (1941). *The Calculi of Lambda Conversion*. Princeton University Press.
   - Original work introducing lambda calculus

5. **Hindley, J. Roger and Seldin, Jonathan P.** (2008). *Lambda-Calculus and Combinators: An Introduction*. Cambridge University Press.
   - Modern introduction with combinatory logic

6. **Sørensen, Morten Heine and Urzyczyn, Paweł** (2006). *Lectures on the Curry-Howard Isomorphism*. Elsevier.
   - Connection between lambda calculus and logic

### Online Resources

7. **Lambda Calculus on Wikipedia**: https://en.wikipedia.org/wiki/Lambda_calculus
   - Good overview and historical context

8. **The Impact of the Lambda Calculus** (Cardone & Hindley, 2006)
   - Historical perspective on lambda calculus
   - https://www.sciencedirect.com/science/article/pii/S1570086806800119

9. **Raúl Rojas - A Tutorial Introduction to the Lambda Calculus**
   - Accessible tutorial with examples
   - https://arxiv.org/abs/1503.09060

## Exercises

1. Implement additional Church encodings (lists, trees)
2. Add α-conversion as an explicit operation
3. Implement the η-reduction rule
4. Add a step-by-step evaluator with visualization
5. Implement the Z combinator and test recursive functions
6. Compare performance of different evaluation strategies
7. Implement DeBruijn indices to avoid variable capture issues
8. Add a REPL (Read-Eval-Print-Loop) for interactive exploration

## Next Chapter

In [Chapter 2](../chapter-02-simply-typed-lambda), we add a simple type system to prevent certain runtime errors and ensure termination.
