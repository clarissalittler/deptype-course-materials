# Chapter 20: Denotational Semantics - Tutorial

This tutorial walks through denotational semantics with step-by-step examples.

## Part 1: What is Denotational Semantics?

### Three Views of Programs

**Operational semantics**: Programs are instructions to follow
```
(λx. x + 1) 3  →  3 + 1  →  4
```
Focus: How does it run?

**Axiomatic semantics**: Programs are logical specifications
```
{x ≥ 0} y := x + 1 {y > 0}
```
Focus: What can we prove?

**Denotational semantics**: Programs are mathematical objects
```
[[(λx. x + 1) 3]] = (λn. n + 1)(3) = 4 ∈ ℕ
```
Focus: What does it *mean*?

### The Denotation Function

We write `[[e]]` for "the denotation of e" — the mathematical meaning.

The denotation function is:
1. **Compositional**: `[[e₁ e₂]]` depends only on `[[e₁]]` and `[[e₂]]`
2. **Abstract**: Ignores evaluation order, focuses on results
3. **Mathematical**: Maps to well-defined mathematical objects

## Part 2: Domains and Bottom

### The Problem of Recursion

Consider:
```
loop = loop        -- diverges
omega = (λx. x x)(λx. x x)  -- diverges
```

What's `[[loop]]`? It can't be a regular number or function—it never produces a value!

### The Solution: Bottom

We introduce a special element **⊥** (bottom) meaning "undefined" or "non-terminating":

```
[[loop]] = ⊥
[[omega]] = ⊥
```

### Domains (CPOs)

A **domain** is a set with:
1. A partial order ⊑ (approximation)
2. A least element ⊥
3. Limits for all increasing chains

### Flat Domains

For base types (Bool, Nat), we use *flat domains*:

```
Bool:           Nat:
  true  false       0   1   2   3   ...
    \    /           \  |  /   /
     \  /             \ | /   /
      ⊥                 ⊥
```

**Key property**: All defined values are incomparable. Only ⊥ is below everything.

### The Approximation Ordering

`d₁ ⊑ d₂` means "d₁ approximates d₂" or "d₂ has at least as much information as d₁":

- `⊥ ⊑ d` for all d (⊥ has no information)
- `n ⊑ n` for all defined n (reflexivity)
- `n ⊑ m` only if n = m (for defined values in flat domains)

## Part 3: Function Domains

### Functions as Semantic Objects

Lambda abstractions denote *functions*. The domain `[A → B]` contains all continuous functions from A to B.

```
[[λx. x + 1]] ∈ [Nat → Nat]
```

### Ordering Functions

Functions are ordered pointwise:
```
f ⊑ g  iff  ∀x. f(x) ⊑ g(x)
```

The least function is:
```
⊥_fun = λx. ⊥     -- undefined everywhere
```

### Continuity

A function f is **continuous** if:
1. Monotone: `x ⊑ y ⟹ f(x) ⊑ f(y)`
2. Preserves limits: `f(⊔ chain) = ⊔ f(chain)`

**Why continuity matters**: It ensures fixed points exist!

## Part 4: Fixed Points

### The Problem

How do we give meaning to recursive definitions?

```
fact = λn. if n=0 then 1 else n * fact(n-1)
```

This is circular! `fact` is defined in terms of itself.

### Kleene's Fixed Point Theorem

**Theorem**: If D is a domain and f : D → D is continuous, then f has a least fixed point:

```
fix f = ⊔ {⊥, f(⊥), f(f(⊥)), f(f(f(⊥))), ...}
      = ⊔ₙ fⁿ(⊥)
```

### Computing Factorial's Fixed Point

Let F = λf. λn. if n=0 then 1 else n * f(n-1)

**Iteration 0**: f₀ = ⊥
```
f₀ = ⊥_fun = λn. ⊥
f₀(0) = ⊥, f₀(1) = ⊥, f₀(2) = ⊥, ...
```

**Iteration 1**: f₁ = F(f₀)
```
f₁ = λn. if n=0 then 1 else n * f₀(n-1)
f₁(0) = 1
f₁(1) = 1 * f₀(0) = 1 * ⊥ = ⊥
f₁(2) = 2 * f₀(1) = 2 * ⊥ = ⊥
```

**Iteration 2**: f₂ = F(f₁)
```
f₂ = λn. if n=0 then 1 else n * f₁(n-1)
f₂(0) = 1
f₂(1) = 1 * f₁(0) = 1 * 1 = 1
f₂(2) = 2 * f₁(1) = 2 * ⊥ = ⊥
```

**Iteration 3**: f₃ = F(f₂)
```
f₃(0) = 1
f₃(1) = 1
f₃(2) = 2 * f₂(1) = 2 * 1 = 2
f₃(3) = ⊥
```

**Pattern**: fₙ is defined on inputs 0 to n-1.

**Limit**: fix F = factorial, defined on all naturals!

### Why It Works

Each iteration fⁿ(⊥) is more defined than the previous:
```
⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ f³(⊥) ⊑ ...
```

The supremum exists (by domain properties) and is the least fixed point.

## Part 5: The Denotation Function

### Variables

```
[[x]]ρ = ρ(x)
```

Look up the variable in the environment ρ (mapping variables to domain elements).

### Lambda Abstraction

```
[[λx. e]]ρ = λd. [[e]]ρ[x↦d]
```

A lambda denotes a function: given d, evaluate the body with x mapped to d.

### Application

```
[[e₁ e₂]]ρ = [[e₁]]ρ ([[e₂]]ρ)
```

Apply the function to the argument.

### Fixed Point

```
[[fix e]]ρ = fix([[e]]ρ)
```

The denotation of fix is the domain-theoretic fixed point.

### Worked Example

Compute `[[((λx. x) true)]]{}`:

```
[[((λx. x) true)]]{}
= [[λx. x]]{}([[true]]{})          -- by application
= (λd. [[x]]{x↦d})(true)           -- by lambda
= (λd. d)(true)                    -- by variable
= true                             -- by function application
```

### Another Example

Compute `[[fix (λf. λx. x)]]{}`:

```
[[fix (λf. λx. x)]]{}
= fix([[λf. λx. x]]{})             -- by fix
= fix(λg. [[λx. x]]{f↦g})          -- by lambda
= fix(λg. λd. [[x]]{f↦g,x↦d})      -- by lambda
= fix(λg. λd. d)                   -- by variable
= λd. d                            -- fixed point of constant function
```

## Part 6: Connecting to Operational Semantics

### The Adequacy Theorem

**Theorem**: If e evaluates to v, then [[e]] = [[v]].

```
e →* v  ⟹  [[e]] = [[v]]
```

This connects the operational and denotational views!

### Example

Operationally:
```
(λx. x + 1) 3  →  3 + 1  →  4
```

Denotationally:
```
[[(λx. x + 1) 3]] = [[λx. x + 1]]([[3]]) = (λn. n+1)(3) = 4 = [[4]]
```

Same result!

### Full Abstraction (The Dream)

We want: e ≃ e' (observationally) ⟺ [[e]] = [[e']]

**Problem**: Standard denotational semantics is *not* fully abstract for PCF! There are functions in the model that don't correspond to any program.

**Solution**: Game semantics, logical relations, or other refined models.

## Practice Problems

### Problem 1: Domain Drawing

Draw the domain for `Bool + Nat` (sum type).

<details>
<summary>Solution</summary>

```
  inl(true)  inl(false)  inr(0)  inr(1)  inr(2)  ...
       \         |         /       |        /
        \        |        /        |       /
         \       |       /         |      /
          ───────┴───────┴─────────┴─────
                        ⊥
```

All defined values are incomparable (flat domain structure for the sum).
</details>

### Problem 2: Fixed Point Iteration

Compute the first 3 iterations for:
```
F = λf. λn. if n=0 then zero else suc(f(pred(n)))
```

<details>
<summary>Solution</summary>

This computes the identity on naturals!

**f₀** = λn. ⊥

**f₁** = λn. if n=0 then 0 else suc(f₀(pred(n)))
- f₁(0) = 0
- f₁(1) = suc(f₀(0)) = suc(⊥) = ⊥
- f₁(n) = ⊥ for n > 0

**f₂** = λn. if n=0 then 0 else suc(f₁(pred(n)))
- f₂(0) = 0
- f₂(1) = suc(f₁(0)) = suc(0) = 1
- f₂(2) = suc(f₁(1)) = suc(⊥) = ⊥

**f₃**:
- f₃(0) = 0
- f₃(1) = 1
- f₃(2) = suc(f₂(1)) = suc(1) = 2
- f₃(3) = ⊥

Pattern: fₙ is the identity on {0, 1, ..., n-1}.
</details>

### Problem 3: Denotation Computation

Compute `[[let x = 2 in x + x]]{}` assuming let x = e₁ in e₂ means (λx. e₂) e₁.

<details>
<summary>Solution</summary>

```
[[let x = 2 in x + x]]{}
= [[(λx. x + x) 2]]{}
= [[λx. x + x]]{}([[2]]{})
= [[λx. x + x]]{}(2)
= (λd. [[x + x]]{x↦d})(2)
= [[x + x]]{x↦2}
= [[x]]{x↦2} + [[x]]{x↦2}
= 2 + 2
= 4
```
</details>
