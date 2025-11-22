# Chapter 2: Common Mistakes and How to Avoid Them

## Introduction

Adding types introduces new ways to make mistakes. This guide helps you avoid common pitfalls when working with STLC.

---

## Mistake #1: Forgetting Type Annotations

### The Mistake

**Wrong**:
```
λx. x   ❌ (This is untyped LC, not STLC!)
```

**Correct**:
```
λx:Bool. x   ✓
λx:Nat. x    ✓
```

### Why It Happens

Coming from Chapter 1, you're used to writing `λx. t`. In STLC, **every** lambda parameter must have a type annotation.

### How to Fix

**Always write the type**: `λx:τ. t`

### Practice

Make these valid STLC terms:
- `λx. λy. x` → ?
- `λf. λx. f x` → ?

<details>
<summary>Answers</summary>

Need to know types! Examples:
- `λx:Nat. λy:Bool. x` (one possibility)
- `λf:Nat→Bool. λx:Nat. f x`

There are many valid typings - the point is you MUST annotate!
</details>

---

## Mistake #2: Wrong Function Type Associativity

### The Mistake

**Wrong thinking**:
```
Nat → Bool → Nat  =  (Nat → Bool) → Nat   ❌
```

**Correct**:
```
Nat → Bool → Nat  =  Nat → (Bool → Nat)   ✓
```

### Why It Matters

```
λx:Nat. λy:Bool. x

Wrong type: (Nat → Bool) → Nat    (function taking a function!)
Right type: Nat → Bool → Nat       (curried function)
```

### The Rule

Function types **associate to the RIGHT**:
```
τ₁ → τ₂ → τ₃  =  τ₁ → (τ₂ → τ₃)
```

This matches currying!

---

## Mistake #3: Type Mismatches in Application

### The Mistake

**Wrong**:
```
(λx:Bool. x) 0   ❌

TYPE ERROR! Function expects Bool, got Nat
```

### How to Recognize

When type checking `t₁ t₂`:
1. Check `t₁`, must get function type `τ₁ → τ₂`
2. Check `t₂`, must get type `τ₁` (exact match!)
3. If types don't match: TYPE ERROR

### Common Examples

```
(λx:Nat. x) true          ❌ (wants Nat, got Bool)
(λx:Bool. x) (succ 0)     ❌ (wants Bool, got Nat)
```

### How to Fix

Check types carefully before applying!

```
Function: λx:Nat. x      Type: Nat → Nat
Argument: 0              Type: Nat
Check: Nat = Nat?        ✓ Yes!
Result: succ x           Type: Nat
```

---

## Mistake #4: Mismatched Conditional Branches

### The Mistake

**Wrong**:
```
if true then 0 else false   ❌

TYPE ERROR! Branches have different types (Nat vs Bool)
```

### The Rule

```
if t₁ then t₂ else t₃
   ^^^      ^^^    ^^^
   Bool      τ      τ   (must be same type!)
```

### Why This Matters

What type should this have?
```
if condition then 0 else false
```

If condition is true, we get `0 : Nat`
If condition is false, we get `false : Bool`

What's the type of the whole expression? Can't be both Nat and Bool!

### How to Fix

Ensure both branches have the same type:

```
if iszero n then 0 else 1          ✓ (both Nat)
if iszero n then true else false   ✓ (both Bool)
if true then (λx:Nat. x) else (λy:Nat. succ y)   ✓ (both Nat → Nat)
```

---

## Mistake #5: Context Confusion

### The Mistake

**Wrong thinking**:
```
Can I type x:Bool ⊢ y : ?

NO! y is not in the context, so we can't type it!
```

### The Rule

**T-Var only works for variables IN the context**:

```
x:τ ∈ Γ
─────────  (T-Var)
Γ ⊢ x : τ
```

### Example

Context: `x:Bool, y:Nat`

- Can type `x`? Yes: `x:Bool, y:Nat ⊢ x : Bool` ✓
- Can type `y`? Yes: `x:Bool, y:Nat ⊢ y : Nat` ✓
- Can type `z`? NO! z not in context ❌

### How Context Extends

In T-Abs, context is extended:

```
Γ, x:τ₁ ⊢ t : τ₂
──────────────────  (T-Abs)
Γ ⊢ λx:τ₁. t : τ₁ → τ₂
```

Example: Type `λx:Bool. x` under empty context

```
x:Bool ⊢ x : Bool      (context extended with x:Bool)
─────────────────────  (T-Abs)
∅ ⊢ λx:Bool. x : Bool → Bool
```

---

## Mistake #6: Shadowing Confusion

### The Mistake

**Confusion**: In `λx:Nat. λx:Bool. x`, which `x` does the body refer to?

**Answer**: The INNER `x:Bool` (shadowing!)

### Example

Type check: `λx:Nat. λx:Bool. x`

```
Step 1: Type inner body x under context x:Nat, x:Bool

x:Bool ∈ {x:Nat, x:Bool}      (inner x shadows outer!)
────────────────────────
x:Nat, x:Bool ⊢ x : Bool

Step 2: Type inner lambda

x:Nat, x:Bool ⊢ x : Bool
────────────────────────────
x:Nat ⊢ λx:Bool. x : Bool → Bool

Step 3: Type outer lambda

x:Nat ⊢ λx:Bool. x : Bool → Bool
──────────────────────────────────────
∅ ⊢ λx:Nat. λx:Bool. x : Nat → Bool → Bool
```

**Result**: Type is `Nat → Bool → Bool` (outer Nat is ignored!)

### Best Practice

Avoid shadowing - use different variable names!

```
Better: λx:Nat. λy:Bool. y
```

---

## Mistake #7: Trying to Type Self-Application

### The Mistake

**Attempting**:
```
λx. x x   (from Chapter 1)
```

**In STLC**:
```
λx:?. x x   ❌ What type for x?
```

### Why It Fails

For `x x` to type check:
- First `x` must have type `τ₁ → τ₂` (it's being applied)
- Second `x` must have type `τ₁` (it's the argument)
- So `x` needs both types: `x : τ₁` AND `x : τ₁ → τ₂`

This is only possible if `τ₁ = τ₁ → τ₂`, which implies `τ₁ = τ₁ → (τ₁ → (...))` - infinite type!

**STLC doesn't allow infinite types**, so `λx. x x` CANNOT be typed.

### Consequence

Can't write Y combinator in STLC:
```
Y = λf. (λx. f (x x)) (λx. f (x x))
             ^^^^^^
             Doesn't type check!
```

---

## Mistake #8: Expecting General Recursion

### The Mistake

**Expecting** to write factorial like Chapter 1:
```
fact = Y (λf. λn. if (iszero n) 1 (mult n (f (pred n))))
   ^
   Y combinator doesn't type check in STLC!
```

### The Reality

STLC is **strongly normalizing** - all programs terminate. Therefore, general recursion is impossible without adding a special construct.

### The Solution

Add an explicit `fix` operator (see exercises):

```
fix : (τ → τ) → τ

factorial = fix (λf:Nat→Nat. λn:Nat.
  if iszero n then 1 else mult n (f (pred n)))
```

### Trade-Off

- **Gain**: Type safety, guaranteed termination
- **Lose**: Can't write general recursive programs (without explicit fix)

---

## Mistake #9: Incorrect Derivation Trees

### The Mistake

**Wrong**: Building derivations top-down without checking premises

### Example

Trying to type `(λx:Bool. x) 0`:

```
WRONG approach:
∅ ⊢ (λx:Bool. x) 0 : Bool   (guessing the result)
```

Let's check if this is valid:

```
We need to apply T-App:

∅ ⊢ λx:Bool. x : ?    ∅ ⊢ 0 : ?
────────────────────────────────
∅ ⊢ (λx:Bool. x) 0 : ?

Left part: λx:Bool. x has type Bool → Bool ✓
Right part: 0 has type Nat ✓

For T-App: function must have type τ₁ → τ₂, argument must have type τ₁

Function type: Bool → Bool
Argument type: Nat

Bool ≠ Nat!   TYPE ERROR! ❌
```

### Correct Approach

**Build derivations bottom-up**:

1. Type leaf nodes (variables, constants)
2. Combine using typing rules
3. Check that premises match

### How to Build Derivations

**Step 1**: Identify the term structure
**Step 2**: Apply appropriate rules from bottom up
**Step 3**: Verify all premises are satisfied

---

## Mistake #10: Confusing Typing and Evaluation

### The Mistake

**Confusion**: "Types change during evaluation"

**Reality**: Types are PRESERVED during evaluation (Preservation theorem!)

### Example

```
⊢ (λx:Nat. succ x) 0 : Nat       (before evaluation)
→ succ 0 : Nat                     (after 1 step)
→ succ 0 : Nat                     (value - still Nat!)
```

Type is `Nat` at every step!

### Key Points

1. **Type checking happens BEFORE evaluation**
2. **Evaluation doesn't change types** (Preservation)
3. **If it type checks, it won't get stuck** (Progress)

### Workflow

```
1. Parse term
2. Type check → Get type τ or TYPE ERROR
3. If TYPE ERROR: reject, don't evaluate
4. If type τ: safe to evaluate
5. Evaluate → get value of type τ
```

---

## Debugging Checklist

When type checking fails:

**1. Type Annotations?**
- [ ] Did I annotate all lambda parameters?
- [ ] Are type annotations in the right place?

**2. Type Matching?**
- [ ] In application, does argument type match function input type?
- [ ] In conditional, do both branches have the same type?

**3. Context?**
- [ ] Is the variable in the context?
- [ ] Am I using the right context for this subterm?

**4. Associativity?**
- [ ] Did I parse function types right-associatively?
- [ ] `Nat → Bool → Nat` = `Nat → (Bool → Nat)`?

**5. Rule Application?**
- [ ] Am I applying the right typing rule?
- [ ] Are all premises satisfied?

**6. Trying to Type Untyped LC?**
- [ ] Am I trying to type `λx. x x` or Y combinator?
- [ ] These don't work in STLC!

---

## Common Type Errors and Fixes

| Error | Example | Fix |
|-------|---------|-----|
| Missing annotation | `λx. x` | `λx:Bool. x` |
| Type mismatch | `(λx:Bool. x) 0` | Use correct type: `(λx:Nat. x) 0` |
| Branch mismatch | `if b then 0 else false` | Same types: `if b then 0 else 1` |
| Variable not in context | `∅ ⊢ x : ?` | Add to context or remove variable |
| Wrong associativity | `(Nat → Bool) → Nat` (wrong) | `Nat → (Bool → Nat)` (right) |

---

## Quick Reference: Typing Rules Checklist

**Variable**:
- [ ] Is `x:τ` in context Γ?

**Abstraction** `λx:τ₁. t`:
- [ ] Can I type `t` under context `Γ, x:τ₁`?
- [ ] If `t : τ₂`, then `λx:τ₁. t : τ₁ → τ₂`

**Application** `t₁ t₂`:
- [ ] Does `t₁` have function type `τ₁ → τ₂`?
- [ ] Does `t₂` have type `τ₁` (exact match)?
- [ ] If yes, result has type `τ₂`

**Conditional** `if t₁ then t₂ else t₃`:
- [ ] Does `t₁` have type `Bool`?
- [ ] Do `t₂` and `t₃` have the SAME type `τ`?
- [ ] If yes, result has type `τ`

---

## Summary

**Top 5 Mistakes**:
1. Forgetting type annotations
2. Wrong function type associativity
3. Type mismatches in application
4. Mismatched conditional branches
5. Trying to type self-application

**Remember**:
- Every lambda needs type annotation
- Function types associate right
- Check types carefully
- Use REPL to verify
- STLC ≠ Untyped LC (no self-application!)

**Keep this guide handy while doing exercises!**
