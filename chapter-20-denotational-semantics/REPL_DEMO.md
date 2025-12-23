# Chapter 20: Denotational Semantics REPL Demo

This file demonstrates the comprehensive REPL for Chapter 20.

## Starting the REPL

```bash
cd chapter-20-denotational-semantics
stack run denotational-repl
```

## Available Commands

### Core Commands
- `<term>` - Compute denotation of a term
- `:help` - Show help message with all commands and syntax
- `:examples` - Show comprehensive examples (12 categories!)
- `:theory` - Show domain theory primer
- `:quit` - Exit the REPL

### Denotation Commands
- `:denote <term>` - Explicitly compute denotation (same as typing term)
- `:eval <term>` - Alias for `:denote`
- `:type <term>` - Show type of term (basic inference)

### Fixed Point Commands
- `:fix n <term>` - Show n iterations of fixed point approximation
- `:fact n` - Compute factorial(n) using fixed points
- `:fib n` - Compute fibonacci(n) using fixed points

### Environment Commands
- `:let x = <term>` - Bind term to variable x
- `:env` - Show current bindings
- `:reset` - Reset all bindings

### Note on Operational Steps
The REPL intentionally does NOT support `:step` and `:steps` commands because denotational semantics is not based on operational evaluation steps. Instead, use:
- `:denote` to compute the semantic value directly
- `:fix n <term>` to see the approximation sequence for fixed points

## Example Session

```
den> true
  [[·]] = True

den> suc 5
  [[·]] = 6

den> (\(x : Nat). suc x) 10
  [[·]] = 11

den> if iszero 0 then 42 else 0
  [[·]] = 42

den> :fact 5
Computing factorial(5)...
[[fact]](5) = 120

den> :fib 10
Computing fibonacci(10)...
[[fib]](10) = 55

den> :fix 3 \(f : Nat -> Nat). \(n : Nat). if iszero n then 0 else suc (f (pred n))
Computing fixed point iterations for: λ(f : Nat → Nat). λ(n : Nat). if iszero n then 0 else suc (f (pred n))
Chain: ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ f³(⊥) ⊑ ...

f^0(⊥) = ⊥
f^1(⊥) = <function>
f^2(⊥) = <function>
f^3(⊥) = <function>

den> :let x = 42
x = 42
[[x]] = 42

den> suc x
  [[·]] = 43

den> :env
Current bindings:
  x = 42  →  [[x]] = 42

den> :reset
Bindings reset.

den> :theory
(Shows comprehensive domain theory primer)

den> :examples
(Shows 12 categories of examples!)

den> :quit
Goodbye!
```

## Key Features

### 1. Comprehensive Help System
- `:help` - Full syntax reference and command guide
- `:examples` - 12 categories of examples covering all language features
- `:theory` - Deep dive into domain theory concepts (CPOs, flat domains, function domains, fixed points)

### 2. Fixed Point Exploration
The `:fix n <term>` command is unique and educational - it shows how fixed points are approximated through iteration:

```
den> :fix 5 \(f : Nat -> Nat). \(x : Nat). if iszero x then 1 else x

f^0(⊥) = ⊥
f^1(⊥) = <function>
f^2(⊥) = <function>
f^3(⊥) = <function>
f^4(⊥) = <function>
f^5(⊥) = <function>
```

This demonstrates the Kleene fixed point theorem: `fix f = ⊔ₙ fⁿ(⊥)`

### 3. Built-in Examples
- `:fact n` - Factorial using `fix`
- `:fib n` - Fibonacci using `fix`

These demonstrate how recursive functions are modeled as least fixed points.

### 4. Environment Management
- Bind terms with `:let x = term`
- View all bindings with `:env`
- Reset with `:reset`
- Uses semantic domains (Dom) for values

### 5. Educational Focus
The REPL is designed for learning denotational semantics:
- Clear separation between syntax (Term) and semantics (Dom)
- Explicit display of denotation function notation `[[·]]`
- Domain theory terminology throughout (⊥, ⊑, ⊔, CPO)
- Comprehensive examples showing all language features

## Example Categories in `:examples`

1. Basic Values (booleans, naturals, unit)
2. Lambda Abstraction (identity, constant functions)
3. Arithmetic (suc, pred, iszero)
4. Conditionals (if-then-else)
5. Let Bindings (simple and nested)
6. Explicit Bottom (⊥ demonstrations)
7. Fixed Points (the heart of recursion!)
8. Factorial (classic recursive example)
9. Fibonacci (another classic)
10. Primitive Recursion (natrec combinator)
11. REPL Environment (:let, :env, :reset)
12. Key Concepts Summary

## Syntax Support

### Terms
- Variables: `x`, `y`, `foo`
- Lambda: `\(x : T). e` or `λ(x : T). e`
- Application: `f x`, `(f x) y`
- Let: `let x = e1 in e2`
- Fix: `fix f`
- If: `if c then t else e`
- Booleans: `true`, `false`
- Naturals: `0`, `suc n`, `pred n`, `iszero n`, or numeric literals `42`
- NatRec: `natrec z s n`
- Unit: `()`, `unit`
- Bottom: `⊥ T`, `bottom T`

### Types
- `Bool` - Boolean type
- `Nat` - Natural number type
- `Unit` - Unit type
- `A -> B` - Function type

## Domain Theory Concepts

The `:theory` command explains:
- **Domains (CPOs)**: Complete Partial Orders with ⊥
- **Flat Domains**: For base types like Nat and Bool
- **Function Domains**: Scott-continuous functions [A → B]
- **Least Fixed Points**: `fix f = ⊔ₙ fⁿ(⊥)` (Kleene's theorem)
- **Approximation Sequence**: Shows how fixed points converge
- **Why Fixed Points Matter**: Recursion as fixed point equations
- **Key Insight**: Programs map to mathematical objects

## Comparison with Other REPLs

Unlike operational REPLs (e.g., Chapter 9 Subtyping):
- No `:step` or `:steps` - denotational semantics is not step-based
- Direct computation of semantic values
- Focus on mathematical meaning rather than evaluation traces
- Fixed point iteration instead of reduction steps

This aligns with the denotational approach: programs denote mathematical objects, and we compute those objects directly rather than simulating execution.

## Educational Value

This REPL demonstrates:
1. **Compositionality**: `[[e1 e2]] = [[e1]]([[e2]])`
2. **Fixed Points for Recursion**: `[[fix f]] = ⊔ₙ fⁿ(⊥)`
3. **Domain Theory**: CPOs, ⊥, approximation ordering
4. **Semantic vs Syntactic**: Clear distinction between Term and Dom
5. **Mathematical Rigor**: Precise meanings for programs

Perfect for students learning how to give mathematical meaning to programming languages!
