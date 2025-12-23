# Chapter 20: Denotational Semantics - Cheat Sheet

## Core Concept

**Denotational semantics** gives programs mathematical meaning by mapping syntax to mathematical objects (domain elements). Unlike operational semantics (how programs run), denotational semantics describes what programs **mean** as mathematical functions.

**Key Insight**: Programs denote domain elements, and recursion is modeled by least fixed points.

## The Denotation Function

```
[[·]] : Syntax → Semantics

Syntax (terms)  ───[[·]]───>  Semantics (domain elements)
```

The semantic brackets `[[·]]` map programs to mathematical objects.

## Domains (CPOs)

A **domain** (Complete Partial Order) is:
1. A set D with a partial order ⊑ (approximation)
2. A least element ⊥ (bottom, "undefined")
3. Suprema exist for all directed sets/chains

### Flat Domains

For base types (Bool, Nat):
```
     0   1   2   3   ...
      \  |  /   /
       \ | /   /
        \|/   /
         ⊥
```

All defined values are incomparable; only ⊥ is below everything.

### Function Domains

```
[A → B] = {f : A → B | f is continuous}
```

Ordered pointwise: `f ⊑ g iff ∀x. f(x) ⊑ g(x)`

Least element: `λx. ⊥` (undefined everywhere)

## The Approximation Ordering (⊑)

```
d₁ ⊑ d₂  means "d₁ approximates d₂" or "d₂ has at least as much information"

Properties:
⊥ ⊑ d           for all d (⊥ is least)
d ⊑ d           (reflexivity)
d₁ ⊑ d₂ ⊑ d₃   implies d₁ ⊑ d₃ (transitivity)
```

In flat domains:
- `⊥ ⊑ v` for all defined values v
- `v ⊑ v` for all v
- `v ⊑ w` only if v = w (for defined values)

## Fixed Points

### Kleene's Fixed Point Theorem

For continuous f : D → D:
```
fix f = ⊔ₙ fⁿ(⊥) = ⊔ {⊥, f(⊥), f(f(⊥)), f(f(f(⊥))), ...}
```

The **Kleene chain**:
```
⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ f³(⊥) ⊑ ...
```

The supremum (⊔) is the **least fixed point**.

### Example: Factorial

```
F = λf. λn. if n=0 then 1 else n * f(n-1)

f⁰(⊥) = λn. ⊥                           (undefined everywhere)
f¹(⊥) = λn. if n=0 then 1 else ⊥        (defined on 0)
f²(⊥) = λn. if n≤1 then ... else ⊥      (defined on 0,1)
f³(⊥) = λn. if n≤2 then ... else ⊥      (defined on 0,1,2)
...
fix F = factorial                        (defined on all naturals)
```

Pattern: fⁿ(⊥) is defined on inputs 0, 1, ..., n-1.

## Denotation Equations

### Variables
```
[[x]]ρ = ρ(x)
```

Look up variable in environment ρ.

### Lambda Abstraction
```
[[λx. e]]ρ = λd ∈ [[A]]. [[e]]ρ[x↦d]
```

A lambda denotes a mathematical function.

### Application
```
[[e₁ e₂]]ρ = [[e₁]]ρ ([[e₂]]ρ)
```

Apply the function to the argument (in the mathematical sense).

### Fixed Point
```
[[fix e]]ρ = fix([[e]]ρ) = ⊔ₙ ([[e]]ρ)ⁿ(⊥)
```

The denotation is the domain-theoretic fixed point.

### Conditional
```
[[if c then t else e]]ρ = cond([[c]]ρ, [[t]]ρ, [[e]]ρ)

where:
  cond(true, t, e) = t
  cond(false, t, e) = e
  cond(⊥, t, e) = ⊥      (strict in condition!)
```

### Arithmetic
```
[[e₁ + e₂]]ρ = [[e₁]]ρ + [[e₂]]ρ    (lifted addition)

where:
  n + m = n+m    (for defined n, m)
  ⊥ + m = ⊥      (strict)
  n + ⊥ = ⊥      (strict)
```

## Continuity

A function f : D → E is **continuous** if:

1. **Monotone**: `d₁ ⊑ d₂ ⟹ f(d₁) ⊑ f(d₂)`
2. **Preserves limits**: `f(⊔ chain) = ⊔ f(chain)`

**Why it matters**: Continuous functions have fixed points!

### Examples

**Continuous**:
- `λx. x` (identity)
- `λx. x + 1` (strict successor)
- `λf. λn. if n=0 then 1 else n * f(n-1)` (factorial combinator)

**Not continuous**:
- `λx. if x=⊥ then 0 else x` (distinguishes ⊥)
- Parallel-or in some models

## Domain Representation in Haskell

```haskell
data Dom
  = DBottom          -- ⊥
  | DBool Bool       -- true, false
  | DNat Integer     -- 0, 1, 2, ...
  | DUnit            -- unit
  | DFun (Dom -> Dom) -- λx. e

-- The approximation ordering
approx :: Dom -> Dom -> Bool
approx DBottom _ = True          -- ⊥ below everything
approx (DBool b1) (DBool b2) = b1 == b2
approx (DNat n1) (DNat n2) = n1 == n2
approx DUnit DUnit = True
approx (DFun f) (DFun g) = -- pointwise comparison
  all (\d -> approx (f d) (g d)) allInputs
approx _ _ = False

-- Fixed point
fix :: (Dom -> Dom) -> Dom
fix f = let x = f x in x  -- Haskell's laziness!
```

Haskell's laziness naturally represents ⊥ as non-termination.

## Key Properties

### Compositionality

The meaning of a compound expression is determined by the meanings of its parts:
```
[[e₁ e₂]]ρ = [[e₁]]ρ ([[e₂]]ρ)
```

Essential for modular reasoning!

### Adequacy

If a term evaluates to a value, they have the same denotation:
```
e →* v  ⟹  [[e]] = [[v]]
```

This connects operational and denotational semantics.

### Full Abstraction (Desired)

Observationally equivalent programs should have equal denotations:
```
e ≃ e'  ⟹  [[e]] = [[e']]
```

Hard to achieve! Standard denotational semantics for PCF is **not** fully abstract.

## Common Patterns

### Pattern 1: Computing Denotations

To compute `[[term]]ρ`:
1. Identify the outermost construct
2. Apply the corresponding denotation equation
3. Recursively compute sub-denotations
4. Combine results

### Pattern 2: Fixed Point Iteration

To understand `fix f`:
1. Start with f⁰(⊥) = ⊥
2. Compute f¹(⊥) = f(⊥)
3. Compute f²(⊥) = f(f(⊥))
4. Continue until pattern is clear
5. The supremum is the fixed point

### Pattern 3: Strictness Analysis

A function is **strict** if `f(⊥) = ⊥`.

Examples:
- `λx. x + 1` is strict
- `λx. λy. x` is strict in first arg, non-strict in second
- `λx. 5` is non-strict (ignores argument)

## Worked Examples

### Example 1: Simple Application

Compute `[[(λx. x) true]]{}`:
```
[[(λx. x) true]]{}
= [[λx. x]]{}([[true]]{})           -- application
= (λd. [[x]]{x↦d})(true)            -- lambda
= (λd. d)(true)                     -- variable
= true                              -- function application
```

### Example 2: Fixed Point

Compute `[[fix (λf. λx. x)]]{}`:
```
[[fix (λf. λx. x)]]{}
= fix([[λf. λx. x]]{})              -- fix
= fix(λg. [[λx. x]]{f↦g})           -- lambda
= fix(λg. λd. [[x]]{f↦g,x↦d})       -- lambda
= fix(λg. λd. d)                    -- variable
= λd. d                             -- fixed point of constant
```

### Example 3: Factorial (First Iterations)

```
F = λf. λn. if n=0 then 1 else n * f(n-1)

F⁰(⊥) = ⊥

F¹(⊥) = F(⊥) = λn. if n=0 then 1 else n * ⊥(n-1)
      = λn. if n=0 then 1 else n * ⊥
      = λn. if n=0 then 1 else ⊥

F²(⊥) = F(F¹(⊥))
      = λn. if n=0 then 1 else n * F¹(⊥)(n-1)
      = λn. if n=0 then 1
            else if n=1 then 1 * 1
            else ⊥

Continuing: fⁿ(⊥)(k) = k! if k < n, else ⊥
```

## Comparison with Other Semantics

| Approach | Question | Main Tool | Pro | Con |
|----------|----------|-----------|-----|-----|
| **Operational** | How to run? | Reduction rules | Concrete, executable | Not compositional |
| **Denotational** | What meaning? | Domain theory | Compositional, abstract | Complex math |
| **Axiomatic** | What to prove? | Logic | Good for verification | Not executable |

## Common Mistakes to Avoid

### Mistake 1: Confusing Syntax and Semantics
- ✗ `[[λx. x]]` is a lambda term
- ✓ `[[λx. x]]` is a mathematical function

### Mistake 2: Forgetting the Environment
- ✗ `[[x]] = x`
- ✓ `[[x]]ρ = ρ(x)`

### Mistake 3: Wrong Iteration Count
- ✗ F³(⊥) defined on 0,1,2,3
- ✓ F³(⊥) defined on 0,1,2 (n iterations → n-1 values)

### Mistake 4: Thinking ⊥ is a Regular Value
- ✗ `⊥ + 1 = 1`
- ✓ `⊥ + 1 = ⊥` (strict arithmetic)

### Mistake 5: Comparing in Flat Domains
- ✗ `1 ⊑ 2` because 1 < 2
- ✓ `1 ⊑ 1` and `2 ⊑ 2`, but 1 and 2 are incomparable

## Extensions

### Products
```
[[⟨e₁, e₂⟩]]ρ = ([[e₁]]ρ, [[e₂]]ρ)

Domain: D₁ × D₂ with pointwise ordering
```

### Sums
```
[[inl e]]ρ = inl([[e]]ρ)
[[inr e]]ρ = inr([[e]]ρ)

Domain: D₁ + D₂ (disjoint union with ⊥)
```

### State
```
Domain: State → (Value × State)

[[e]]ρ : Store → (Dom × Store)
```

### Continuations
```
Domain: [A → Answer] (CPS transform)

[[(λx. e)]]ρ = λk. k(λd. [[e]]ρ[x↦d])
```

## Quick Reference

### Domain Basics
- **⊥**: Undefined/non-terminating
- **⊑**: Approximation ordering
- **⊔**: Supremum (least upper bound)
- **Flat domain**: Only ⊥ below defined values

### Fixed Points
- **Kleene chain**: ⊥, f(⊥), f²(⊥), ...
- **fix f**: Supremum of Kleene chain
- **Iteration n**: Defined on n-1 inputs (for factorial-like)

### Key Equations
```
[[x]]ρ = ρ(x)
[[λx. e]]ρ = λd. [[e]]ρ[x↦d]
[[e₁ e₂]]ρ = [[e₁]]ρ ([[e₂]]ρ)
[[fix e]]ρ = fix([[e]]ρ)
```

### Continuity
- Monotone: preserve ⊑
- Preserve limits: f(⊔ chain) = ⊔ f(chain)

## Historical Context

Developed by **Dana Scott** and **Christopher Strachey** in the late 1960s. Scott invented domain theory to give meaning to lambda calculus with recursion—solving a long-standing problem.

**Key insight**: Functions must be continuous to ensure fixed points exist.

## Further Reading

1. **Scott & Strachey** - "Toward a Mathematical Semantics" (1971)
   - Foundational paper

2. **Winskel** - "The Formal Semantics of Programming Languages" (1993)
   - Excellent textbook

3. **Gunter** - "Semantics of Programming Languages" (1992)
   - Comprehensive treatment

4. **Abramsky & Jung** - "Domain Theory" (1994)
   - Modern survey

## Debugging Checklist

When denotational semantics confuses you:
1. Check domains: Right domain for each type?
2. Check environment: Threading ρ correctly?
3. Check comparisons: Only ⊥ below in flat domains?
4. Check fixed points: Counting iterations correctly?
5. Check composition: `[[e₁ e₂]]ρ = [[e₁]]ρ ([[e₂]]ρ)`

## Next Steps

After mastering denotational semantics:
- Study **logical relations** for program equivalence
- Explore **game semantics** for full abstraction
- Learn **effect semantics** (monads, state)
- Connect to **domain-theoretic realizability**
