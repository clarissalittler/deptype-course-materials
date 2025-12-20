# Chapter 2: Simply Typed Lambda Calculus - Frequently Asked Questions

## Table of Contents

1. [Conceptual Questions](#conceptual-questions)
2. [Types and Typing](#types-and-typing)
3. [Type Checking](#type-checking)
4. [Type Safety](#type-safety)
5. [Limitations](#limitations)
6. [Practical "I'm Stuck" Scenarios](#practical-im-stuck-scenarios)

---

## Conceptual Questions

### Q1: Why add types? Untyped lambda calculus worked fine!

**A**: Types give us **guarantees**:

| Untyped | Simply Typed |
|---------|--------------|
| `(λx. x x)(λx. x x)` loops forever | Can't even write this! |
| Might apply number to number | Type error before running |
| Runtime crashes possible | "Well-typed programs don't go wrong" |

Types are a **static analysis** that catches bugs before execution.

### Q2: What does "simply typed" mean?

**A**: "Simple" because types are... simple:
```
τ ::= Base | τ → τ
```
Just base types and function types. No polymorphism, no fancy features.

Compare to later chapters:
- Hindley-Milner: Polymorphism (`∀a. a → a`)
- System F: Explicit type abstraction
- Dependent types: Types that depend on values

### Q3: What's the key insight of STLC?

**A**: **Types classify terms by behavior**:
- `Nat`: things that compute to numbers
- `Bool`: things that compute to booleans
- `Nat → Bool`: functions from numbers to booleans

A well-typed term tells you what it will produce!

### Q4: What is Curry-Howard correspondence for STLC?

**A**: Types are propositions, programs are proofs!

| Type | Proposition |
|------|-------------|
| `A → B` | "A implies B" |
| `A → A` | "A implies A" (tautology) |
| `(A → B) → (B → C) → (A → C)` | Transitivity of implication |

If you can write a program of type `A → B`, you've proved A implies B!

---

## Types and Typing

### Q5: Why do lambda parameters need type annotations?

**A**: Without annotations, we can't infer types uniquely:
```
λx. x    -- Is this Nat → Nat? Bool → Bool? (A → A) → (A → A)?
```

STLC requires annotations: `λx:Nat. x` is unambiguously `Nat → Nat`.

(Chapter 4 shows how to infer types automatically!)

### Q6: What's a typing context (Γ)?

**A**: A mapping from variables to types:
```
Γ = {x: Nat, y: Bool, f: Nat → Bool}
```

When type-checking `x`, we look up its type in Γ.

### Q7: How do I read typing judgments?

**A**: `Γ ⊢ t : τ` means "in context Γ, term t has type τ".

```
{x: Nat} ⊢ x : Nat           -- x has type Nat (from context)
{} ⊢ λx:Nat. x : Nat → Nat   -- Lambda has function type
```

### Q8: What's the difference between `→` in types vs terms?

**A**:
- **In types**: `→` is the function type constructor: `Nat → Bool`
- **In terms**: We write `λx:τ. t` for lambda, `f x` for application

Types describe, terms compute!

### Q9: Can I have functions that take functions?

**A**: Yes! **Higher-order functions**:
```
λf:Nat→Nat. λx:Nat. f (f x)
: (Nat → Nat) → Nat → Nat
```
This takes a function `f` and applies it twice.

---

## Type Checking

### Q10: How does type checking work?

**A**: Recursively check each subterm:

1. **Variable**: Look up in context
2. **Lambda** `λx:τ₁. t`: Check `t` with `x:τ₁` added to context, return `τ₁ → τ₂`
3. **Application** `t₁ t₂`: Check `t₁ : τ₁ → τ₂` and `t₂ : τ₁`, return `τ₂`
4. **If** `if t₁ then t₂ else t₃`: Check `t₁ : Bool`, check `t₂` and `t₃` have same type

### Q11: What errors can type checking catch?

**A**:
- **Type mismatch**: `if 5 then ...` (5 is not Bool)
- **Argument type wrong**: `(λx:Nat. x) true` (Bool ≠ Nat)
- **Not a function**: `5 3` (can't apply Nat to Nat)
- **Undefined variable**: `x` when x not in context

### Q12: Why check types at compile time, not run time?

**A**: Compile-time checking is:
- **Faster**: Catch errors before running
- **Complete**: All paths checked, not just executed ones
- **Documented**: Types are machine-checked documentation

Runtime checks (dynamic typing) only catch errors when hit.

---

## Type Safety

### Q13: What does "type safety" mean?

**A**: Two properties:

1. **Progress**: Well-typed non-value can always step
   - "Well-typed programs don't get stuck"

2. **Preservation**: Stepping preserves type
   - "Types don't change during execution"

Together: **Well-typed programs don't go wrong!**

### Q14: What's the Progress theorem?

**A**: If `⊢ t : τ` then either:
- `t` is a value (done computing), OR
- `t → t'` for some `t'` (can take a step)

**Never stuck!** No "undefined behavior".

### Q15: What's the Preservation theorem?

**A**: If `⊢ t : τ` and `t → t'`, then `⊢ t' : τ`.

**Types are preserved!** A `Nat` always evaluates to a `Nat`.

### Q16: Does type safety mean no errors?

**A**: No! Type safety means no **type** errors. You can still have:
- Division by zero (if you add division)
- Infinite loops (if you add recursion)
- Logic bugs (wrong algorithm)

Types catch a specific class of errors, not all errors.

---

## Limitations

### Q17: What CAN'T I express in STLC?

**A**: Several things:

1. **Polymorphism**: Can't write `id : ∀a. a → a`
2. **Recursion**: No Y combinator (can't type `λx. x x`)
3. **Self-application**: `f f` is untypeable
4. **Data structures**: No lists, trees without extensions

### Q18: Why can't I write a polymorphic identity function?

**A**: STLC has no type variables! You must pick a concrete type:
```
λx:Nat. x    : Nat → Nat
λx:Bool. x   : Bool → Bool
```

You can't write ONE function that works for all types. That requires System F (Chapter 5).

### Q19: Why can't I write factorial?

**A**: Factorial needs recursion, but STLC guarantees termination!

**Solution**: Add a `fix` combinator as a primitive:
```
fix : (τ → τ) → τ
fix f = f (fix f)
```

This lets you write:
```
factorial = fix (λf:Nat→Nat. λn:Nat.
  if iszero n then 1 else mult n (f (pred n)))
```

### Q20: STLC seems limited. Why study it?

**A**: STLC is the **foundation**:
- Every type system extends STLC
- Type checking algorithms start here
- Type safety proofs follow this pattern

Master STLC, and advanced systems are just variations!

---

## Practical "I'm Stuck" Scenarios

### Q21: "Type mismatch: expected Bool, got Nat"

**A**: You're using a number where a boolean is expected:
```
if 5 then ...    -- 5 is Nat, not Bool
```

**Fix**: Use a boolean expression:
```
if iszero n then ...
```

### Q22: "Argument type mismatch"

**A**: Function expects one type, you gave another:
```
(λx:Nat. succ x) true    -- true is Bool, not Nat
```

**Fix**: Check the function's parameter type and provide matching argument.

### Q23: "Not a function type"

**A**: You're trying to apply something that isn't a function:
```
5 3    -- Can't apply Nat to Nat
true 5 -- Can't apply Bool to Nat
```

**Fix**: Make sure the first thing in application is a function.

### Q24: "How do I express let bindings?"

**A**: `let x = e1 in e2` is syntactic sugar for application:
```
let x = e1 in e2  ≡  (λx:τ. e2) e1
```

Where τ is the type of e1.

### Q25: "How do I write multi-argument functions?"

**A**: Use currying (nested lambdas):
```
-- add : Nat → Nat → Nat
λm:Nat. λn:Nat. ...

-- Apply: add 3 5
(add 3) 5
```

### Q26: "My code type checks but gives wrong answer"

**A**: Types don't prevent logic bugs! Common issues:
- Arguments in wrong order
- Off-by-one errors
- Wrong base case

**Debug**: Test with simple inputs, trace by hand.

---

## Quick Reference: Typing Rules

```
x:τ ∈ Γ
─────────── (T-Var)
Γ ⊢ x : τ

Γ, x:τ₁ ⊢ t : τ₂
─────────────────────────── (T-Abs)
Γ ⊢ (λx:τ₁. t) : τ₁ → τ₂

Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : τ₁
─────────────────────────────────── (T-App)
Γ ⊢ t₁ t₂ : τ₂

Γ ⊢ t₁ : Bool    Γ ⊢ t₂ : τ    Γ ⊢ t₃ : τ
────────────────────────────────────────────── (T-If)
Γ ⊢ if t₁ then t₂ else t₃ : τ
```

---

## Further Reading

- **Pierce TAPL Chapters 8-9**: Definitive STLC reference
- **Harper PFPL Chapter 4**: Alternative presentation
- **Curry & Feys (1958)**: Original simply typed lambda calculus

**Remember**: STLC trades expressiveness for safety. Every extension in later chapters builds on this foundation!
