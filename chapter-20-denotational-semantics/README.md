# Chapter 20: Denotational Semantics

## Overview

Denotational semantics gives meaning to programs by mapping syntax to mathematical
objects called *domains*. Unlike operational semantics (which describes how programs
execute) or axiomatic semantics (which describes what programs prove), denotational
semantics describes *what programs mean* as mathematical functions.

The key insight: **programs denote elements of mathematical domains, and recursion
is modeled by least fixed points**.

## The Central Idea

```
Syntax (terms)  ───[[·]]───>  Semantics (domain elements)

    λx. e        ──────>      λd. [[e]][x↦d]
    e1 e2        ──────>      [[e1]]([[e2]])
    fix f        ──────>      ⊔ₙ fⁿ(⊥)
```

The *denotation function* `[[·]]` is a compositional mapping from syntax to semantics.

## Domain Theory

### What is a Domain?

A **domain** (or CPO - Complete Partial Order) is:
1. A set D with a partial order ⊑ (approximation)
2. A least element ⊥ (bottom, representing "undefined")
3. Suprema for all directed sets

### Flat Domains

For base types, we use *flat domains*:

```
     0   1   2   3   ...
      \  |  /   /
       \ | /   /
        \|/   /
         ⊥
```

All defined values are incomparable; only ⊥ is below everything.

### Function Domains

The domain `[A → B]` consists of all **continuous functions** from A to B:
- A function f is continuous if it preserves suprema of directed sets
- Ordered pointwise: f ⊑ g iff ∀x. f(x) ⊑ g(x)
- The least element is `λx. ⊥`

## The Fixed Point Theorem

**Kleene's Fixed Point Theorem:** If D is a domain and f : D → D is continuous,
then f has a least fixed point:

```
fix f = ⊔ₙ fⁿ(⊥) = ⊔ {⊥, f(⊥), f(f(⊥)), f(f(f(⊥))), ...}
```

This chain is called the *Kleene chain*, and its supremum is the least fixed point.

### Why This Matters

Consider factorial:
```
fact = fix (λf. λn. if n=0 then 1 else n * f(n-1))
```

The iterations:
- `f⁰(⊥) = ⊥` (undefined everywhere)
- `f¹(⊥) = λn. if n=0 then 1 else ⊥` (defined only on 0)
- `f²(⊥) = λn. if n=0 then 1 else if n=1 then 1 else ⊥` (defined on 0,1)
- ...
- `fix f = factorial` (defined on all naturals)

## Denotation Equations

### Variables
```
[[x]]ρ = ρ(x)
```

### Abstraction
```
[[λx:A. e]]ρ = λd ∈ [[A]]. [[e]]ρ[x↦d]
```

### Application
```
[[e1 e2]]ρ = [[e1]]ρ ([[e2]]ρ)
```

### Fixed Point
```
[[fix e]]ρ = ⊔ₙ ([[e]]ρ)ⁿ(⊥)
```

### Conditional
```
[[if c then t else e]]ρ = cond([[c]]ρ, [[t]]ρ, [[e]]ρ)
where cond(true, t, e) = t
      cond(false, t, e) = e
      cond(⊥, t, e) = ⊥
```

## Implementation

### Domain Representation

```haskell
data Dom
  = DBottom          -- ⊥
  | DBool Bool       -- Booleans
  | DNat Integer     -- Natural numbers
  | DUnit            -- Unit
  | DFun (Dom -> Dom) -- Functions
```

Haskell's laziness naturally represents ⊥ as non-termination.

### Fixed Point in Haskell

```haskell
fix :: (Dom -> Dom) -> Dom
fix f = let x = f x in x
```

This works because Haskell is lazy!

### The Denotation Function

```haskell
denote :: Env -> Term -> Dom
denote env (Var x) = lookupEnv x env
denote env (Lam x _ body) = DFun $ \d -> denote (extend x d env) body
denote env (App e1 e2) = domApp (denote env e1) (denote env e2)
denote env (Fix f) = fix $ \d -> case denote env f of
                                   DFun g -> g d
```

## File Structure

```
chapter-20-denotational-semantics/
├── src/
│   ├── Syntax.hs       -- Terms and types
│   ├── Domain.hs       -- Semantic domains
│   ├── Denotation.hs   -- [[·]] function
│   ├── Parser.hs       -- Parser
│   └── Pretty.hs       -- Pretty printing
├── app/
│   └── Main.hs         -- Interactive REPL
├── test/
│   └── Spec.hs         -- Test suite
└── exercises/
    └── EXERCISES.md    -- Practice problems
```

## Building and Running

```bash
cd chapter-20-denotational-semantics
stack build
stack test
stack exec denotational-repl
```

## REPL Examples

```
den> 5
Term: suc (suc (suc (suc (suc 0))))
[[·]] = 5

den> (\(x : Nat). suc x) 3
Term: (λ(x : Nat). suc x) suc (suc (suc 0))
[[·]] = 4

den> :fact 5
[[fact]](5) = 120

den> :fib 10
[[fib]](10) = 55

den> :theory
[Shows domain theory explanation]
```

## Key Properties

### Compositionality

The meaning of a compound expression is determined by the meanings of its parts:
```
[[e1 e2]] = [[e1]]([[e2]])
```

This is essential for modular reasoning about programs.

### Adequacy

If two terms have different denotations, they are observationally distinguishable:
```
[[e]] ≠ [[e']] ⟹ e ≇ e'
```

### (Desired) Full Abstraction

Observationally equivalent programs have equal denotations:
```
e ≃ e' ⟹ [[e]] = [[e']]
```

This is harder to achieve and fails for PCF with the standard semantics!

## Comparison with Other Semantics

| Approach | Question Answered | Main Tool |
|----------|------------------|-----------|
| **Operational** | How does it run? | Reduction rules |
| **Denotational** | What does it mean? | Domain theory |
| **Axiomatic** | What can we prove? | Logic, pre/postconditions |

### Relationship to Operational Semantics

The fundamental theorem relates the two:
```
e →* v  ⟹  [[e]] = [[v]]
```

Evaluation preserves meaning!

## Historical Context

Denotational semantics was developed by Dana Scott and Christopher Strachey in
the late 1960s. Scott invented domain theory specifically to give meaning to
lambda calculus with recursion—a problem that had resisted earlier attempts.

The key insight was that functions should be *continuous* (preserve limits),
which ensures that recursive definitions have solutions.

## Advanced Topics (Not Covered)

- **Game Semantics**: Full abstraction for PCF
- **Logical Relations**: For proving properties of denotations
- **Effect Semantics**: Monads, continuation semantics
- **Domain-Theoretic Realizability**: Connection to computability

## References

1. **Scott & Strachey** - "Toward a Mathematical Semantics for Computer Languages" (1971)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=17137872945485770728)
   - The foundational paper on denotational semantics

2. **Plotkin** - "LCF Considered as a Programming Language" (1977)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=11177537545871788543)
   - Connects denotational and operational semantics

3. **Winskel** - "The Formal Semantics of Programming Languages" (1993)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=5166942826655615986)
   - Standard textbook, excellent domain theory chapter

4. **Gunter** - "Semantics of Programming Languages" (1992)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=2384742488457606323)
   - Comprehensive mathematical treatment

5. **Amadio & Curien** - "Domains and Lambda-Calculi" (1998)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=8562128591577102889)
   - Deep mathematical foundations

6. **Abramsky & Jung** - "Domain Theory" (1994)
   - [Google Scholar](https://scholar.google.com/scholar?cluster=1883405295920867780)
   - Modern survey of domain theory

## Exercises

See `exercises/EXERCISES.md` for:
- Computing denotations by hand
- Drawing domain diagrams
- Fixed point iteration exercises
- Continuity proofs
- Extensions (products, state, continuations)

## Tests

Run the test suite:
```bash
stack test
```

Tests cover:
- Basic value denotations (booleans, naturals, unit)
- Function application
- Conditionals
- Fixed points and recursion (factorial, fibonacci)
- Domain operations
- Parser and pretty printer
