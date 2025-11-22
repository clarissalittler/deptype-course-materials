# Chapter 4: Common Mistakes and How to Avoid Them

## Introduction

Hindley-Milner type inference is elegant but subtle. Students consistently make the same mistakes when learning it. This guide identifies these pitfalls and shows you how to avoid them.

**Use this guide**:
- When your type inference gives unexpected results
- When you don't understand why something doesn't type check
- When unification fails mysteriously
- As a reference while doing exercises

---

## Mistake #1: Forgetting the Occurs Check (CRITICAL!)

### The Mistake

**Problem**: Allowing `α = α → τ` or similar infinite types.

**Wrong**:
```
unify(α, α → Nat) = [α ↦ α → Nat]  ❌ WRONG!
```

**Why it's wrong**: This creates an infinite type:
```
α = α → Nat
  = (α → Nat) → Nat
  = ((α → Nat) → Nat) → Nat
  = (((α → Nat) → Nat) → Nat) → Nat
  = ... INFINITE!
```

### How to Recognize It

You're at risk when unifying:
1. A type variable `α`
2. With a type `τ` that contains `α`

**Examples to watch for**:
```
unify(α, α → β)           -- FAIL
unify(α, List α)          -- FAIL
unify(α, β → α)           -- FAIL
unify(α, (α → β) → γ)     -- FAIL
```

### How to Fix It

**Always check before binding `α ↦ τ`**:

```
bindVar α τ:
  if α == τ:
    return []                    -- α = α, trivial
  else if α ∈ freeVars(τ):
    FAIL "Occurs check"          -- α occurs in τ, infinite type!
  else:
    return [α ↦ τ]              -- Safe to bind
```

### Practice Problems

Which of these should fail the occurs check?

1. `unify(α, Nat)`
2. `unify(α, β)`
3. `unify(α, α)`
4. `unify(α, α → α)`
5. `unify(α → β, γ → α)`

<details>
<summary>Answers</summary>

1. ✓ OK - α doesn't occur in Nat
2. ✓ OK - α doesn't occur in β (different variable)
3. ✓ OK - trivial case, return []
4. ✗ FAIL - α occurs in α → α
5. ✓ OK - neither α nor β occur on the right side in problematic ways
   - Result: [α ↦ γ, β ↦ α]... wait, that's wrong!
   - Actually: [γ ↦ α, β ↦ α] after proper unification

</details>

### Real Example

**Inferring**: `λx. x x` (self-application)

```
Step 1: x has fresh type α
Step 2: First x: type α
Step 3: Second x: type α
Step 4: Application: unify(α, α → β)
  ❌ FAIL! α occurs in α → β

ERROR: Cannot construct infinite type α = α → β
```

This is why self-application doesn't type check in HM!

---

## Mistake #2: Confusing Let and Lambda

### The Mistake

**Problem**: Expecting lambda-bound variables to be polymorphic.

**Wrong Expectation**:
```
(λid. (id true, id 0)) (λx. x)
-- "id should be polymorphic, right?" ❌ WRONG!
```

**Why it's wrong**: Only **let** generalizes. Lambda variables are **monomorphic**.

### The Rule

**Let-polymorphism**:
```
let id = λx. x in (id true, id 0)
✓ Works! id : ∀α. α → α
```

**Lambda-monomorphism**:
```
(λid. (id true, id 0)) (λx. x)
✗ Fails! id : β → β (must pick one β)
```

### Why The Difference?

**Technical reason**:
- Let-bindings are second-class (can't be passed around)
- Safe to generalize because we see all uses at once
- Lambda parameters are first-class (passed around)
- Generalizing them requires System F (undecidable inference)

**Practical reason**:
```
-- This is OK:
let f = λx. x in someFunction f

-- If f were polymorphic, someFunction would receive ∀α. α → α
-- But someFunction's type can't say "takes a polymorphic function"
-- That's higher-rank types (System F territory)
```

### How to Fix It

**Use let when you need polymorphism**:

Wrong:
```
(λmap. ...) (λf. λlist. ...)
-- map is monomorphic!
```

Right:
```
let map = λf. λlist. ... in ...
-- map is polymorphic!
```

### Detailed Example

**Attempt**: Infer type of `(λid. (id 5, id true)) (λx. x)`

```
Step 1: Infer function type
  id gets fresh variable α
  Γ = {id : α}

Step 2: Infer (id 5)
  id : α
  Need: unify(α, Nat → β)
  S₁ = [α ↦ Nat → β]
  Result: β

Step 3: Infer (id true)
  id : S₁(α) = Nat → β
  Need: unify(Nat → β, Bool → γ)
  unify(Nat, Bool) ❌ FAIL!

ERROR: Cannot unify Nat with Bool
```

**With let**:
```
let id = λx. x in (id 5, id true)

Step 1: Infer λx. x → α → α
Step 2: Generalize → ∀α. α → α
Step 3: Γ = {id : ∀α. α → α}
Step 4: Use id at 5:
  Instantiate: β → β
  Unify: (β → β, Nat → γ) → [β ↦ Nat, γ ↦ Nat]
  Result: Nat
Step 5: Use id at true:
  Instantiate: δ → δ (fresh! different from β)
  Unify: (δ → δ, Bool → ε) → [δ ↦ Bool, ε ↦ Bool]
  Result: Bool
Step 6: Pair: Nat × Bool ✓
```

### Quick Test

If you're unsure whether something should be let or lambda:

**Ask**: Do I need the variable to have different types at different uses?
- **Yes** → Use let
- **No** → Lambda is fine

---

## Mistake #3: Not Threading Substitutions

### The Mistake

**Problem**: Forgetting to apply substitutions from sub-derivations.

**Wrong**:
```
-- Inferring: t₁ t₂
τ₁, S₁ = infer(Γ, t₁)
τ₂, S₂ = infer(Γ, t₂)        ❌ WRONG! Should be infer(S₁(Γ), t₂)
S₃ = unify(τ₁, τ₂ → α)       ❌ WRONG! Should unify S₂(τ₁)
```

**Why it's wrong**: We learn about type variables as we go. Must use what we learned!

### The Correct Pattern

**Right**:
```
-- Inferring: t₁ t₂
τ₁, S₁ = infer(Γ, t₁)
τ₂, S₂ = infer(S₁(Γ), t₂)     ✓ Apply S₁ to environment!
S₃ = unify(S₂(τ₁), τ₂ → α)    ✓ Apply S₂ to τ₁!
return (S₃(α), S₃ ∘ S₂ ∘ S₁)  ✓ Compose all substitutions!
```

### Example: Where It Goes Wrong

**Inferring**: `(λf. f) (λx. x)`

**Wrong approach**:
```
Step 1: Infer λf. f
  Result: α → α, S₁ = []

Step 2: Infer λx. x (WRONG: not applying S₁)
  Result: β → β, S₂ = []

Step 3: Unify (WRONG: not applying S₂ to first type)
  unify(α → α, (β → β) → γ)
  unify(α, β → β) → [α ↦ β → β]
  unify(α, γ) ... wait, α is already bound!

This gets messy fast.
```

**Right approach**:
```
Step 1: Infer λf. f
  Result: α → α, S₁ = []

Step 2: Apply S₁ to environment: S₁(Γ) = Γ (no change)
  Infer λx. x
  Result: β → β, S₂ = []

Step 3: Apply S₂ to first type: S₂(α → α) = α → α
  Unify: unify(α → α, (β → β) → γ)
  S₃ = [α ↦ β → β, γ ↦ β → β]

Step 4: Result type: S₃(γ) = β → β
  Final substitution: S₃ ∘ S₂ ∘ S₁ = S₃
```

### Mnemonic

**"Thread the needle"**: Substitutions flow through like thread through a needle:
1. Learn something → substitution S₁
2. Apply S₁ to everything you do next
3. Learn more → substitution S₂
4. Compose: S₂ ∘ S₁
5. Repeat

---

## Mistake #4: Wrong Substitution Composition Order

### The Mistake

**Problem**: Composing substitutions in the wrong order.

**Wrong**:
```
S₁ = [α ↦ Nat]
S₂ = [β ↦ α]

Wrong: S₂ ∘ S₁  ❌
```

**Why it's wrong**: Composition order matters! `S₁ ∘ S₂` means "apply S₂ first, then S₁".

### The Rule

**Right to left**: `(S₁ ∘ S₂)(τ) = S₁(S₂(τ))`

Apply S₂ first, then S₁.

**In Algorithm W**: If you infer with S₁, then S₂, compose as `S₂ ∘ S₁`.

### Example

```
S₁ = [α ↦ Nat]
S₂ = [β ↦ α]

S₁ ∘ S₂:
  For β: S₂(β) = α, then S₁(α) = Nat
  Result: [α ↦ Nat, β ↦ Nat]

S₂ ∘ S₁:
  For β: S₁(β) = β, then S₂(β) = α
  Result: [α ↦ Nat, β ↦ α]

Different results! Order matters!
```

### In Algorithm W

```
τ₁, S₁ = infer(Γ, t₁)      -- First inference
τ₂, S₂ = infer(S₁(Γ), t₂)  -- Second inference
S₃ = unify(...)             -- Unification

Final: S₃ ∘ S₂ ∘ S₁         -- Reverse order of discovery!
```

**Why reverse?** When we apply the final substitution, we want to:
1. Apply what we learned first (S₁)
2. Then what we learned second (S₂)
3. Then what we learned last (S₃)

So we compose right-to-left.

---

## Mistake #5: Generalizing Too Much

### The Mistake

**Problem**: Generalizing variables that are free in the environment.

**Wrong**:
```
Γ = {x : α}

generalize(Γ, α → β) = ∀α β. α → β  ❌ WRONG!
```

**Why it's wrong**: α is free in Γ, so it represents a **specific** (though unknown) type. We can't make it polymorphic!

### The Rule

```
generalize(Γ, τ) = ∀ᾱ. τ
  where ᾱ = freeVars(τ) \ freeVars(Γ)
```

Only generalize variables that are:
- Free in τ
- NOT free in Γ

### Example

```
Γ = {f : α → α, x : β}

Type to generalize: α → β → γ

Step 1: Free in type: {α, β, γ}
Step 2: Free in environment: {α, β}
Step 3: Can generalize: {γ} only

Result: ∀γ. α → β → γ
```

### Why This Matters

**Scenario**: Inside a function
```
λf. let id = λx. x in ...

Environment when we generalize id:
  Γ = {f : α}

If id's type is α → α:
  generalize(Γ, α → α) = α → α (NO generalization!)

Because α is free in Γ - it's f's type!
```

---

## Mistake #6: Misunderstanding Instantiation

### The Mistake

**Problem**: Reusing the same type variables when instantiating.

**Wrong**:
```
σ = ∀α. α → α

First use: instantiate(σ) = β → β
Second use: instantiate(σ) = β → β  ❌ Same β! WRONG!
```

**Why it's wrong**: Each instantiation should get **fresh** variables.

### The Rule

**Each instantiation gets independent fresh variables**:

```
σ = ∀α. α → α

First use: instantiate(σ) = β → β    (β fresh)
Second use: instantiate(σ) = γ → γ   (γ fresh, different from β!)
```

### Example

```
let id = λx. x in (id true, id 0)

id has type ∀α. α → α

First use (id true):
  inst(∀α. α → α) = β → β
  unify(β → β, Bool → γ)
  Result: Bool

Second use (id 0):
  inst(∀α. α → α) = δ → δ   (fresh δ, not β!)
  unify(δ → δ, Nat → ε)
  Result: Nat

Different instantiations → works!
```

### If You Reuse Variables

```
Wrong: both uses get β → β

First use (id true):
  unify(β → β, Bool → γ) → [β ↦ Bool]

Second use (id 0):
  Already decided β = Bool!
  unify(Bool → Bool, Nat → ε) → FAIL!
```

---

## Mistake #7: Expecting Polymorphic Lambdas

### The Mistake

**Problem**: Writing code that requires first-class polymorphism.

**Wrong Expectation**:
```
applyTwice = λf. (f 0, f true)
-- "f should work at both Nat and Bool!" ❌
```

**Why it's wrong**: f is lambda-bound, so it's monomorphic!

### What Happens

```
Step 1: f gets type α
Step 2: (f 0): unify(α, Nat → β) → α = Nat → β
Step 3: (f true): unify(Nat → β, Bool → γ) → FAIL!

Cannot unify Nat with Bool.
```

### The Limitation

**Hindley-Milner limitation**: Cannot express "function taking a polymorphic function".

In System F (Chapter 5), you can write:
```
applyTwice : (∀α. α → α) → Nat × Bool
```

But not in HM!

### Workarounds

**Option 1**: Use let (if possible)
```
let f = λx. x in applyTwice f
-- f is generalized before being passed
```

**Option 2**: Pass multiple specialized versions
```
applyTwice : (Nat → Nat) → (Bool → Bool) → Nat × Bool
```

**Option 3**: Use existential types or modules (advanced)

---

## Mistake #8: Confusing Type Inference with Type Checking

### The Mistake

**Problem**: Thinking type inference is just "checking without annotations".

**Reality**: Type inference is more powerful!

### The Difference

**Type checking** (STLC):
- You provide types
- Compiler verifies they're correct
- No creativity needed

**Type inference** (HM):
- Compiler figures out types
- Solves equations (unification)
- Finds most general type (principal type)

### Example

**STLC**: You must say:
```
λf:(Nat→Nat). λx:Nat. f x
```

**HM**: Compiler figures out:
```
λf. λx. f x  has type  ∀α β. (α → β) → α → β
```

Much more general than you might have written!

### Why It Matters

Don't think: "What type would I give this?"

Think: "What's the most general type that works?"

The inferencer finds the most general type automatically!

---

## Mistake #9: Ignoring Occurs Check Failures

### The Mistake

**Problem**: Not understanding why certain terms fail to type.

**Confused by**:
```
λx. x x  -- "Why doesn't this work?"
```

### The Answer

```
Step 1: x has type α
Step 2: First x: α
Step 3: Second x: α
Step 4: x x: unify(α, α → β)
Step 5: ❌ FAIL! Occurs check.

α would need to equal α → β, which is infinite.
```

### Terms That Hit This

**Self-application**:
```
λx. x x                    -- FAIL
λf. f f                    -- FAIL
```

**Y combinator** (naive version):
```
λf. (λx. f (x x)) (λx. f (x x))  -- FAIL
```

**Omega combinator**:
```
(λx. x x) (λx. x x)        -- FAIL
```

### Why No Infinite Types?

**Theoretical**: Types represent structure. Infinite structure is undefined.

**Practical**: Cannot generate code for infinite type.

**Design**: HM is designed to be decidable and terminate.

---

## Mistake #10: Not Simplifying Types

### The Mistake

**Problem**: Leaving types in complicated form.

**Example**:
```
After inference: (β → γ) → (α → β) → α → γ
"Is this the same as compose?" 🤔
```

### The Fix

**Rename variables systematically**:
```
(β → γ) → (α → β) → α → γ

Rename: β → a, γ → b, α → c
Result: (a → b) → (c → a) → c → b

Wait, that's weird. Let me redo:
Original: (β → γ) → (α → β) → α → γ

This is: take function (β→γ), function (α→β), value α
  Apply second to value: β
  Apply first to result: γ

Renaming to standard: (b → c) → (a → b) → a → c
That's composition!
```

### Standard Variable Names

**Convention**:
- Simple types: α, β, γ
- Compose type: (β → γ) → (α → β) → α → γ
- Map type: (α → β) → List α → List β

Following conventions helps recognize standard patterns.

---

## Debugging Strategies

### When Unification Fails

1. **Check occurs check**: Is a variable being unified with a type containing itself?
2. **Trace unification**: Do it step-by-step by hand
3. **Look for base type conflicts**: Nat vs Bool, etc.
4. **Check if you need let**: Maybe it's a let-polymorphism issue

### When You Get Unexpected Types

1. **Check substitution threading**: Did you apply substitutions correctly?
2. **Check composition order**: Right order for composition?
3. **Verify generalization**: Did you generalize at the right time?
4. **Check instantiation**: Are you using fresh variables?

### When Something "Should Work"

1. **Is it first-class polymorphism?**: HM can't do that
2. **Is it self-application?**: HM can't do that either
3. **Did you use let?**: Maybe you need let-polymorphism
4. **Check the REPL**: Verify your intuition

---

## Quick Reference: Common Error Messages

**"Occurs check fails"**
- Trying to create infinite type
- Often from self-application
- Can't be fixed in HM

**"Cannot unify Nat with Bool"**
- Using value at incompatible types
- Check if you need let-polymorphism
- Maybe a logic error?

**"Variable not found"**
- Typo in variable name
- Scope issue

**"Cannot generalize free variable"**
- Trying to generalize variable in environment
- Check your generalization logic

---

## Summary: The Big Three

### 1. Occurs Check
Always check before binding `α ↦ τ` that `α ∉ freeVars(τ)`.

### 2. Let-Polymorphism
Only `let` generalizes. Lambda parameters are monomorphic.

### 3. Thread Substitutions
Apply what you learned: `infer(S₁(Γ), t₂)` not `infer(Γ, t₂)`.

**Master these three and most mistakes disappear!**

---

## Practice: Spot the Mistakes

Try to find the errors in these inference attempts (answers below):

1. `unify(α, List α) = [α ↦ List α]`
2. `(λid. id 5 + id true) (λx. x)`
3. `generalize({x:α}, α → α) = ∀α. α → α`
4. Inferring `λf. f (f 0)` gives `(Nat → Nat) → Nat`

<details>
<summary>Answers</summary>

1. ❌ Occurs check! α occurs in List α
2. ❌ Let-polymorphism needed! id is monomorphic in lambda
3. ❌ Can't generalize α! It's free in environment
4. ❌ Too specific! Should be `∀α. (α → α) → α`

</details>

---

**Remember**: Mistakes are how we learn. Consult this guide whenever you're stuck, and soon these patterns will become second nature!
