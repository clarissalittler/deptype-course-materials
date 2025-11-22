# Chapter 2: Simply Typed Lambda Calculus - Tutorial

## Introduction

Welcome to STLC! In Chapter 1, you learned lambda calculus where anything goes. In this chapter, we add **types** to reject bad programs before they run.

**The Big Idea**: Types let us prove properties about programs *before* running them. "Well-typed programs don't go wrong!"

---

## Part 1: Type Syntax and Intuition

### What is a Type?

A type describes what kind of value an expression produces.

**Basic types**:
- `Bool` - boolean values (true, false)
- `Nat` - natural numbers (0, 1, 2, ...)

**Function types**:
- `τ₁ → τ₂` - functions from τ₁ to τ₂

### Examples

| Expression | Type | Meaning |
|------------|------|---------|
| `true` | `Bool` | A boolean value |
| `0` | `Nat` | A natural number |
| `λx:Bool. x` | `Bool → Bool` | Function from Bool to Bool |
| `λx:Nat. succ x` | `Nat → Nat` | Function from Nat to Nat |
| `λx:Bool. 0` | `Bool → Nat` | Takes Bool, returns Nat |

### Function Type Syntax

Function types **associate to the right**:
```
Nat → Bool → Nat  =  Nat → (Bool → Nat)
```

This makes sense with currying:
```
λx:Nat. λy:Bool. x
```
Type: `Nat → (Bool → Nat)` - takes Nat, returns function that takes Bool and returns Nat

### Key Difference from Chapter 1

**Chapter 1 (Untyped)**:
```
λx. x
```

**Chapter 2 (Typed)**:
```
λx:Bool. x         (identity on Booleans)
λx:Nat. x          (identity on Nats)
```

Each typed version is a DIFFERENT function!

---

## Part 2: Typing Contexts and Variables

### What is a Context?

A **typing context** (written Γ) maps variables to their types. Think of it as "assumptions" about variables.

**Example contexts**:
```
∅                  empty context (no variables)
x:Bool             x has type Bool
x:Bool, y:Nat      x has type Bool, y has type Nat
```

### The T-Var Rule

To type check a variable, look it up in the context:

```
x:τ ∈ Γ
─────────  (T-Var)
Γ ⊢ x : τ
```

**Example 1**: Type check `x` under context `x:Bool`
```
x:Bool ∈ {x:Bool}
─────────────────  (T-Var)
x:Bool ⊢ x : Bool
```
✓ `x` has type `Bool`

**Example 2**: Type check `y` under context `x:Bool, y:Nat`
```
y:Nat ∈ {x:Bool, y:Nat}
───────────────────────  (T-Var)
x:Bool, y:Nat ⊢ y : Nat
```
✓ `y` has type `Nat`

### Worked Example

Question: Under context `f:Nat→Bool, x:Nat`, what is the type of `f`?

Answer:
```
f:Nat→Bool ∈ {f:Nat→Bool, x:Nat}
────────────────────────────────  (T-Var)
f:Nat→Bool, x:Nat ⊢ f : Nat→Bool
```

`f` has type `Nat→Bool` ✓

---

## Part 3: Lambda Abstraction (T-Abs)

### The Rule

```
Γ, x:τ₁ ⊢ t : τ₂
──────────────────────  (T-Abs)
Γ ⊢ λx:τ₁. t : τ₁ → τ₂
```

**Reading**: If, assuming `x` has type `τ₁`, the body `t` has type `τ₂`, then the whole function has type `τ₁ → τ₂`.

### Example 1: Identity on Booleans

Type check: `λx:Bool. x`

```
Step 1: To type λx:Bool. x, we need to type the body x under context x:Bool

x:Bool ∈ {x:Bool}
─────────────────  (T-Var)
x:Bool ⊢ x : Bool

Step 2: Apply T-Abs

x:Bool ⊢ x : Bool
────────────────────────  (T-Abs)
∅ ⊢ λx:Bool. x : Bool → Bool
```

**Result**: `λx:Bool. x` has type `Bool → Bool` ✓

### Example 2: Constant Function

Type check: `λx:Nat. λy:Bool. x`

```
Step 1: Type the outer lambda body: λy:Bool. x

  Need to type this under context x:Nat

  Step 1a: Type the inner lambda body: x

  x:Nat ∈ {x:Nat, y:Bool}
  ───────────────────────  (T-Var)
  x:Nat, y:Bool ⊢ x : Nat

  Step 1b: Apply T-Abs for inner lambda

  x:Nat, y:Bool ⊢ x : Nat
  ────────────────────────────────  (T-Abs)
  x:Nat ⊢ λy:Bool. x : Bool → Nat

Step 2: Apply T-Abs for outer lambda

x:Nat ⊢ λy:Bool. x : Bool → Nat
──────────────────────────────────────────  (T-Abs)
∅ ⊢ λx:Nat. λy:Bool. x : Nat → (Bool → Nat)
```

**Result**: Type is `Nat → Bool → Nat` ✓

---

## Part 4: Application (T-App)

### The Rule

```
Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : τ₁
────────────────────────────────  (T-App)
Γ ⊢ t₁ t₂ : τ₂
```

**Reading**: If `t₁` is a function from `τ₁` to `τ₂`, and `t₂` has type `τ₁`, then applying `t₁` to `t₂` produces a value of type `τ₂`.

**Critical**: The argument type must match!

### Example 1: Simple Application

Type check: `(λx:Bool. x) true`

```
Part 1: Type the function λx:Bool. x

x:Bool ⊢ x : Bool
────────────────────────  (T-Abs)
∅ ⊢ λx:Bool. x : Bool → Bool

Part 2: Type the argument true

──────────────────  (T-True)
∅ ⊢ true : Bool

Part 3: Apply T-App

∅ ⊢ λx:Bool. x : Bool → Bool    ∅ ⊢ true : Bool
──────────────────────────────────────────────  (T-App)
∅ ⊢ (λx:Bool. x) true : Bool
```

**Result**: Type is `Bool` ✓

### Example 2: Type Error

Try to type check: `(λx:Bool. x) 0`

```
Part 1: Function type

∅ ⊢ λx:Bool. x : Bool → Bool

Part 2: Argument type

∅ ⊢ 0 : Nat

Part 3: Try T-App

∅ ⊢ λx:Bool. x : Bool → Bool    ∅ ⊢ 0 : Nat
?????????????????????????????????????????????

ERROR! Function expects Bool but got Nat!
```

**Result**: TYPE ERROR ❌

This is the whole point of types - catch this error before running!

### Example 3: Curried Application

Type check: `(λx:Nat. λy:Bool. x) 0 true`

```
Step 1: Type (λx:Nat. λy:Bool. x) 0

  1a: Function type: Nat → Bool → Nat
  1b: Argument type: Nat
  1c: Apply T-App: Result type is Bool → Nat

Step 2: Type ((λx:Nat. λy:Bool. x) 0) true

  2a: Function type (from step 1): Bool → Nat
  2b: Argument type: Bool
  2c: Apply T-App: Result type is Nat
```

**Result**: Type is `Nat` ✓

---

## Part 5: Conditionals

### The Rule

```
Γ ⊢ t₁ : Bool    Γ ⊢ t₂ : τ    Γ ⊢ t₃ : τ
────────────────────────────────────────  (T-If)
Γ ⊢ if t₁ then t₂ else t₃ : τ
```

**Key points**:
1. Condition must be `Bool`
2. Both branches must have the SAME type τ
3. Result has that type τ

### Example 1: Valid Conditional

Type check: `if true then 0 else 1`

```
Condition:
──────────────────  (T-True)
∅ ⊢ true : Bool

Then branch:
──────────────  (T-Zero)
∅ ⊢ 0 : Nat

Else branch:
────────────────  (T-Succ on T-Zero...)
∅ ⊢ 1 : Nat

Apply T-If:
∅ ⊢ true : Bool    ∅ ⊢ 0 : Nat    ∅ ⊢ 1 : Nat
─────────────────────────────────────────────  (T-If)
∅ ⊢ if true then 0 else 1 : Nat
```

**Result**: Type is `Nat` ✓

### Example 2: Type Error - Mismatched Branches

Try to type check: `if true then 0 else false`

```
∅ ⊢ true : Bool    ∅ ⊢ 0 : Nat    ∅ ⊢ false : Bool
???????????????????????????????????????????????????

ERROR! Branches have different types (Nat vs Bool)!
```

**Result**: TYPE ERROR ❌

### Example 3: Conditional with Functions

Type check: `if true then (λx:Nat. x) else (λy:Nat. succ y)`

```
Condition: Bool ✓

Then branch: Nat → Nat ✓

Else branch: Nat → Nat ✓

Result: Nat → Nat ✓
```

Both branches are functions with the same type - valid!

---

## Part 6: Natural Numbers

### Typing Rules

```
────────────  (T-Zero)
Γ ⊢ 0 : Nat

Γ ⊢ t : Nat
─────────────────  (T-Succ)
Γ ⊢ succ t : Nat

Γ ⊢ t : Nat
─────────────────  (T-Pred)
Γ ⊢ pred t : Nat

Γ ⊢ t : Nat
──────────────────────  (T-IsZero)
Γ ⊢ iszero t : Bool
```

### Examples

Type check: `succ (succ 0)`

```
──────────────  (T-Zero)
∅ ⊢ 0 : Nat
───────────────────  (T-Succ)
∅ ⊢ succ 0 : Nat
──────────────────────────  (T-Succ)
∅ ⊢ succ (succ 0) : Nat
```

Type check: `iszero (pred (succ 0))`

```
∅ ⊢ 0 : Nat
─────────────────  (T-Succ)
∅ ⊢ succ 0 : Nat
───────────────────────  (T-Pred)
∅ ⊢ pred (succ 0) : Nat
───────────────────────────────────  (T-IsZero)
∅ ⊢ iszero (pred (succ 0)) : Bool
```

---

## Part 7: Complete Example - Putting It All Together

Let's type check a complex term: `λf:Nat→Bool. λx:Nat. f (succ x)`

### Step-by-Step Derivation

```
Goal: ∅ ⊢ λf:Nat→Bool. λx:Nat. f (succ x) : ?

Step 1: Type the outer lambda body: λx:Nat. f (succ x)
        Context: f:Nat→Bool

  Step 1.1: Type the inner lambda body: f (succ x)
            Context: f:Nat→Bool, x:Nat

    Step 1.1.1: Type f

    f:Nat→Bool ∈ {f:Nat→Bool, x:Nat}
    ────────────────────────────────  (T-Var)
    f:Nat→Bool, x:Nat ⊢ f : Nat→Bool

    Step 1.1.2: Type (succ x)

      x:Nat ∈ {f:Nat→Bool, x:Nat}
      ───────────────────────────  (T-Var)
      f:Nat→Bool, x:Nat ⊢ x : Nat
      ───────────────────────────────────  (T-Succ)
      f:Nat→Bool, x:Nat ⊢ succ x : Nat

    Step 1.1.3: Type application f (succ x)

    f:Nat→Bool, x:Nat ⊢ f : Nat→Bool    f:Nat→Bool, x:Nat ⊢ succ x : Nat
    ────────────────────────────────────────────────────────────────────  (T-App)
    f:Nat→Bool, x:Nat ⊢ f (succ x) : Bool

  Step 1.2: Type inner lambda

  f:Nat→Bool, x:Nat ⊢ f (succ x) : Bool
  ─────────────────────────────────────────────────  (T-Abs)
  f:Nat→Bool ⊢ λx:Nat. f (succ x) : Nat → Bool

Step 2: Type outer lambda

f:Nat→Bool ⊢ λx:Nat. f (succ x) : Nat → Bool
──────────────────────────────────────────────────────────────  (T-Abs)
∅ ⊢ λf:Nat→Bool. λx:Nat. f (succ x) : (Nat→Bool) → (Nat → Bool)
```

**Final Type**: `(Nat → Bool) → (Nat → Bool)`

**Interpretation**: Takes a function from Nat to Bool, returns a function from Nat to Bool. This is a "higher-order function"!

---

## Part 8: Evaluation

### The Good News

Evaluation works almost exactly like Chapter 1!

**Call-by-value β-reduction**:
```
(λx:τ. t) v  →  [x ↦ v]t
```

The type annotation doesn't change evaluation - it's just checked before we evaluate.

### Example: Identity

Evaluate: `(λx:Bool. x) true`

```
(λx:Bool. x) true
→ [x ↦ true]x
→ true
```

### Example: Application

Evaluate: `(λx:Nat. succ x) 0`

```
(λx:Nat. succ x) 0
→ [x ↦ 0](succ x)
→ succ 0
```

### Example: Conditional

Evaluate: `if iszero 0 then 1 else 2`

```
if iszero 0 then 1 else 2
→ if true then 1 else 2       (iszero 0 → true)
→ 1                            (select then branch)
```

### Key Insight

Once a program type checks, evaluation is safe! Types guarantee:
- No "stuck" states
- No runtime type errors
- Terminates (strong normalization)

---

## Part 9: Type Safety (Progress + Preservation)

### Progress Theorem

**Theorem**: If `⊢ t : τ`, then either:
1. `t` is a value, OR
2. `t → t'` for some `t'`

**Plain language**: Well-typed programs never get stuck.

**Example**:
- `true` is a value ✓
- `(λx:Bool. x) true` can step to `true` ✓
- `if true then 0 else 1` can step to `0` ✓

Non-examples (not well-typed):
- `(λx:Bool. x) 0` - doesn't type check!
- `true 0` - doesn't type check!

### Preservation Theorem

**Theorem**: If `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`

**Plain language**: Types are preserved by evaluation.

**Example**:
```
⊢ (λx:Nat. succ x) 0 : Nat     (initial term)
→ succ 0 : Nat                  (after one step)
→ succ 0 : Nat                  (value - still type Nat!)
```

### Together: Type Safety

Progress + Preservation = "Well-typed programs don't go wrong"

1. **Progress** says: never stuck
2. **Preservation** says: type doesn't change

Together: well-typed programs safely evaluate to values of the right type!

---

## Part 10: Strong Normalization and Expressiveness

### Strong Normalization

**Theorem**: Every well-typed STLC term terminates.

**Proof idea**: Types prevent self-application, which prevents infinite loops.

**Examples of terms that DON'T type check**:
```
λx. x x                      (can't type - would need x : τ and x : τ → σ)
(λx. x x) (λx. x x)          (Ω - infinite loop from Chapter 1)
```

### The Trade-Off

**What we gained**:
- Type safety
- Guaranteed termination
- Early error detection

**What we lost**:
- Can't write `λx. x x` (self-application)
- Can't write general recursion (yet!)
- STLC is NOT Turing-complete

### Can't Write General Recursion

In Chapter 1, we had the Y combinator. In STLC, it doesn't type check:

```
Y = λf. (λx. f (x x)) (λx. f (x x))
             ^^^^^^
             This part doesn't type check!
```

**Solution**: We'll add a `fix` construct in the exercises!

---

## Part 11: Common Patterns

### Higher-Order Functions

```
compose : (Nat → Bool) → (Bool → Nat) → Bool → Bool
compose = λf. λg. λx. f (g x)
```

Takes two functions and composes them!

### Partial Application

```
add : Nat → Nat → Nat
add = λx. λy. x + y          (+ isn't built-in, but imagine it is)

add5 : Nat → Nat
add5 = add 5
```

Partial application still works with types!

---

## Part 12: Practical Type Checking

### Algorithm

To type check `t` under context `Γ`:

1. **Variable `x`**: Look up `x` in `Γ`
2. **Abstraction `λx:τ₁. t`**:
   - Check body `t` under context `Γ, x:τ₁`
   - If body has type `τ₂`, result is `τ₁ → τ₂`
3. **Application `t₁ t₂`**:
   - Check `t₁`, get type `τ₁`
   - Check `t₂`, get type `τ₂`
   - If `τ₁ = τ₂ → τ₃`, result is `τ₃`
   - Otherwise, TYPE ERROR
4. **Conditional `if t₁ then t₂ else t₃`**:
   - Check `t₁`, must be `Bool`
   - Check `t₂`, get type `τ`
   - Check `t₃`, must also be `τ`
   - Result is `τ`

### Decision Procedure

Type checking is **decidable** - there's an algorithm that always terminates with yes/no.

This is different from type *inference* (coming in Chapter 4!), where we figure out types without annotations.

---

## Summary: Key Takeaways

1. **Types prevent errors**: Bad programs rejected before running
2. **Typing rules are syntax-directed**: Easy to check
3. **Progress + Preservation = Type Safety**: "Well-typed programs don't go wrong"
4. **Strong Normalization**: All STLC programs terminate
5. **Trade-off**: Safety vs. expressiveness (can't write Y combinator)
6. **Foundation for more**: STLC is the basis for all modern typed languages

---

## What's Next?

**Chapter 3: STLC with ADTs**
- Add product types (pairs, tuples)
- Add sum types (tagged unions)
- Pattern matching
- Build real data structures!

**Chapter 4: Hindley-Milner Type Inference**
- Remove type annotations
- Let the computer figure out types
- Polymorphism!
