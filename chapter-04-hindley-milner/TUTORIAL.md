# Chapter 4: Hindley-Milner Type Inference - Tutorial

## Introduction

Welcome to the tutorial for Chapter 4! This is where type systems get really exciting. You'll learn how compilers can **automatically figure out types** without you writing a single type annotation, while maintaining complete type safety.

Think of this tutorial as your personal guide through one of computer science's most elegant algorithms. We'll take it step by step, building intuition before diving into formalism.

---

## Part 1: Type Variables - The Foundation

### What Are Type Variables?

In Chapter 2, you wrote explicit types like `Bool → Bool` or `Nat → Nat`. But what if you want a function that works for **any** type?

**Chapter 2 (STLC)**: Write separate identity functions
```
idBool  = λx:Bool. x    : Bool → Bool
idNat   = λx:Nat. x     : Nat → Nat
idPair  = λx:Nat×Nat. x : Nat×Nat → Nat×Nat
```

**Chapter 4 (Hindley-Milner)**: Write ONE identity function
```
id = λx. x              : ∀α. α → α
```

The `α` is a **type variable** - it stands for "any type". When you use `id`, you can instantiate `α` to whatever type you need.

### Type Variables in Action

**Example**: The const function
```haskell
const = λx. λy. x
```

What's its type?
- `x` can be any type - call it `α`
- `y` can be any type - call it `β`
- The result is `x`, so it has type `α`
- Overall type: `α → β → α`

Read as: "Give me any two types α and β. I'll take an α, then a β, and return an α."

### Monotypes vs Polytypes

**Monotype** (no ∀): Simple types with variables
```
α
Nat
α → β
Bool → α
(α → β) → α → β
```

**Polytype** (with ∀): Type schemes with quantifiers
```
∀α. α → α
∀α β. α → β → α
∀α β γ. (β → γ) → (α → β) → α → γ
```

**Key**: When we say `id : ∀α. α → α`, we mean "id works for ALL types α".

### Practice: Reading Type Variables

Let's practice reading types with variables:

**Type 1**: `α → α`
- Function from some type to the same type
- Examples: identity, square, negate

**Type 2**: `α → β → α`
- Takes two arguments of possibly different types
- Returns the first one
- Example: const

**Type 3**: `(α → β) → α → β`
- Takes a function and an argument
- Applies the function to the argument
- Example: apply function

**Type 4**: `(β → γ) → (α → β) → α → γ`
- Takes two functions and composes them
- Example: compose function

---

## Part 2: Type Substitutions - Solving for Variables

### What Is a Type Substitution?

A substitution is like a solution to an equation. If you have an equation `x + 3 = 5`, the substitution is `[x ↦ 2]`.

Similarly, if you have a type equation `α = Nat`, the substitution is `[α ↦ Nat]`.

**Definition**: A substitution `S` maps type variables to types:
```
S = [α₁ ↦ τ₁, α₂ ↦ τ₂, ..., αₙ ↦ τₙ]
```

### Applying Substitutions

**Rule**: Replace all occurrences of the variable with its binding.

**Example 1**: `[α ↦ Nat](α → α)`
```
Step 1: Replace left α with Nat → Nat → α
Step 2: Replace right α with Nat → Nat → Nat
Result: Nat → Nat
```

**Example 2**: `[α ↦ Bool, β ↦ Nat](α → β)`
```
Step 1: Replace α with Bool → Bool → β
Step 2: Replace β with Nat → Bool → Nat
Result: Bool → Nat
```

**Example 3**: `[α ↦ β → γ](α → α)`
```
Replace α with β → γ
Result: (β → γ) → (β → γ)
```

### Substitution Composition

Sometimes we need to apply substitutions in sequence. This is **composition**.

**Definition**: `(S₁ ∘ S₂)(τ)` = `S₁(S₂(τ))`

Apply `S₂` first, then apply `S₁` to the result.

**Example**:
```
S₁ = [α ↦ Nat]
S₂ = [β ↦ α]

What is S₁ ∘ S₂?

For β: S₂(β) = α, then S₁(α) = Nat
So: (S₁ ∘ S₂)(β) = Nat

Result: S₁ ∘ S₂ = [α ↦ Nat, β ↦ Nat]
```

**Warning**: Composition is NOT commutative! `S₁ ∘ S₂` ≠ `S₂ ∘ S₁` in general.

### Practice Problems

Try these:

1. `[α ↦ Nat](α → Bool → α)`
2. `[α ↦ Nat, β ↦ Bool](α → β → α)`
3. `[α ↦ β](α → α)`

<details>
<summary>Solutions</summary>

1. `Nat → Bool → Nat`
2. `Nat → Bool → Nat`
3. `β → β`

</details>

---

## Part 3: Unification - Solving Type Equations

### The Unification Problem

**Question**: Given two types `τ₁` and `τ₂`, can we find a substitution `S` such that `S(τ₁) = S(τ₂)`?

**Example**: Unify `α → Bool` with `Nat → β`
```
We need: S(α → Bool) = S(Nat → β)

This means:
- S(α) = Nat
- S(Bool) = S(β)
- Since Bool has no variables: S(β) = Bool

Solution: S = [α ↦ Nat, β ↦ Bool]
```

### Robinson's Unification Algorithm

Here's the algorithm step by step:

**Base Cases**:
```
unify(τ, τ) = []                    (same type - no substitution needed)
unify(α, τ) = [α ↦ τ]               (if α doesn't occur in τ)
unify(τ, α) = [α ↦ τ]               (symmetric)
```

**Recursive Case** (function types):
```
unify(τ₁ → τ₂, τ₃ → τ₄):
  S₁ = unify(τ₁, τ₃)                (unify argument types)
  S₂ = unify(S₁(τ₂), S₁(τ₄))       (unify result types with S₁ applied)
  return S₂ ∘ S₁
```

**Failure**:
```
unify(Nat, Bool) = FAIL             (different base types)
unify(α, τ) = FAIL                  (if α occurs in τ - occurs check!)
```

### Worked Example 1: Simple Unification

**Unify** `α → β` with `Nat → Bool`

```
Step 1: These are both function types, so:
  unify(α → β, Nat → Bool)
  = unify argument types and result types

Step 2: Unify arguments:
  S₁ = unify(α, Nat) = [α ↦ Nat]

Step 3: Unify results (with S₁ applied):
  S₂ = unify(S₁(β), S₁(Bool))
     = unify(β, Bool)
     = [β ↦ Bool]

Step 4: Compose:
  S₂ ∘ S₁ = [α ↦ Nat, β ↦ Bool]
```

**Check**: `[α ↦ Nat, β ↦ Bool](α → β)` = `Nat → Bool` ✓

### Worked Example 2: Recursive Unification

**Unify** `α → α` with `β → Nat`

```
Step 1: Function types
  unify(α → α, β → Nat)

Step 2: Unify arguments:
  S₁ = unify(α, β) = [α ↦ β]

Step 3: Unify results with S₁:
  S₂ = unify(S₁(α), S₁(Nat))
     = unify(β, Nat)
     = [β ↦ Nat]

Step 4: Compose:
  S₂ ∘ S₁ = [α ↦ Nat, β ↦ Nat]
```

### The Occurs Check

**Problem**: What if we try to unify `α` with `α → β`?

```
unify(α, α → β) = [α ↦ α → β]  ???
```

If we allow this, we get:
```
α = α → β
  = (α → β) → β
  = ((α → β) → β) → β
  = ...
  INFINITE TYPE!
```

**Solution**: The **occurs check** - before binding `α ↦ τ`, verify that `α` doesn't appear in `τ`.

```
unify(α, α → β) = FAIL  (α occurs in α → β)
unify(α, β → α) = FAIL  (α occurs in β → α)
```

### Practice: Unification

Try these (answers below):

1. `unify(α, Nat)`
2. `unify(α → β, Bool → Bool)`
3. `unify(α → α, Nat → β)`
4. `unify(α, α → Nat)`  (Watch out!)
5. `unify((α → β) → γ, (Nat → Bool) → α)`

<details>
<summary>Solutions</summary>

1. `[α ↦ Nat]`
2. `[α ↦ Bool, β ↦ Bool]`
3. `[α ↦ Nat, β ↦ Nat]`
4. **FAIL** (occurs check)
5. `[α ↦ Nat, β ↦ Bool, γ ↦ Nat]`

</details>

---

## Part 4: Type Schemes - Capturing Polymorphism

### What Is a Type Scheme?

A **type scheme** (or **polytype**) explicitly marks which variables are polymorphic:

```
∀α. α → α           (polymorphic in α)
∀α β. α → β → α     (polymorphic in α and β)
```

The `∀` (forall) means "for all types α (and β)".

### Generalization: Creating Type Schemes

**Generalization** converts a monotype to a polytype by quantifying free variables:

```
generalize(Γ, τ) = ∀ᾱ. τ
  where ᾱ = ftv(τ) \ ftv(Γ)
```

**Translation**: Quantify variables that are free in `τ` but NOT free in the environment `Γ`.

**Example 1**: Empty environment
```
generalize(∅, α → α)
  = ∀α. α → α

All variables in τ are free, environment has no variables.
```

**Example 2**: Variable in environment
```
Γ = {f : α → α}

generalize(Γ, α → β)
  = ∀β. α → β

α is free in Γ, so we DON'T quantify it.
Only β is quantified.
```

**Why?** If `α` is free in Γ, it represents a **specific** (but unknown) type. We can't generalize it!

### Instantiation: Using Type Schemes

**Instantiation** creates fresh type variables for each use:

```
instantiate(∀α β. α → β) = γ → δ    (γ, δ fresh)
```

**Example**: Multiple uses of identity
```
let id = λx. x in (id true, id 0)

Step 1: Infer type of λx. x → α → α
Step 2: Generalize → ∀α. α → α
Step 3: Use id at true:
  Instantiate: ∀α. α → α → β → β  (β fresh)
  Unify: β → β with Bool → ?
  Result: Bool → Bool
Step 4: Use id at 0:
  Instantiate: ∀α. α → α → γ → γ  (γ fresh, different from β!)
  Unify: γ → γ with Nat → ?
  Result: Nat → Nat
```

Each use gets **independent** fresh variables!

### Practice: Generalization

Given `Γ = {x : α, y : β}`, what is:

1. `generalize(Γ, α → α)`
2. `generalize(Γ, γ → γ)`
3. `generalize(Γ, α → β → γ)`

<details>
<summary>Solutions</summary>

1. `α → α` (no quantification - α is free in Γ)
2. `∀γ. γ → γ` (γ not in Γ, quantify it)
3. `∀γ. α → β → γ` (only γ is quantified)

</details>

---

## Part 5: Algorithm W Step-by-Step

### The Big Picture

Algorithm W infers types by:
1. **Generating constraints** (what types must be equal)
2. **Solving constraints** (via unification)
3. **Threading substitutions** (keeping track of what we've learned)

### The Rules

**W-Var**: Looking up variables
```
Γ, x:σ ⊢ x : inst(σ) ⇝ []

Translation:
- Look up x in environment, get type scheme σ
- Instantiate σ with fresh variables
- No new constraints (substitution is empty)
```

**W-Abs**: Lambda abstraction
```
Γ, x:α ⊢ t : τ ⇝ S    (α fresh)
───────────────────────────────
Γ ⊢ λx. t : S(α) → τ ⇝ S

Translation:
- Assume x has fresh type variable α
- Infer type of body t, getting type τ and substitution S
- Result type: S(α) → τ (apply S to the parameter type!)
- Return the substitution S
```

**W-App**: Application
```
Γ ⊢ t₁ : τ₁ ⇝ S₁
S₁(Γ) ⊢ t₂ : τ₂ ⇝ S₂
S₃ = unify(S₂(τ₁), τ₂ → α)    (α fresh)
────────────────────────────────────────
Γ ⊢ t₁ t₂ : S₃(α) ⇝ S₃ ∘ S₂ ∘ S₁

Translation:
- Infer type of function t₁ → τ₁, S₁
- Apply S₁ to environment (we learned something!)
- Infer type of argument t₂ → τ₂, S₂
- Unify: S₂(τ₁) should be τ₂ → (result type)
- Return S₃(α) where α is the result type
- Compose all substitutions
```

**W-Let**: Let binding (THE SPECIAL ONE!)
```
Γ ⊢ t₁ : τ₁ ⇝ S₁
S₁(Γ), x:gen(S₁(Γ), τ₁) ⊢ t₂ : τ₂ ⇝ S₂
────────────────────────────────────────
Γ ⊢ let x = t₁ in t₂ : τ₂ ⇝ S₂ ∘ S₁

Translation:
- Infer type of bound expression t₁ → τ₁, S₁
- GENERALIZE τ₁ to get type scheme!
- Add x with type scheme to environment
- Infer type of body t₂
- Return composition of substitutions
```

### Worked Example 1: Identity Function

**Infer type of** `λx. x`

```
Step 1: W-Abs - we have a lambda
  Need to infer type of body (x) with x in environment

Step 2: Create fresh type variable for x
  α fresh
  Environment: Γ = {x : α}

Step 3: Infer type of body x
  W-Var: x:α ⊢ x : α ⇝ []
  (Look up x, get α, no constraints)

Step 4: Apply W-Abs
  Result type: S(α) → α where S = []
  So: α → α

Step 5: Generalize (at top level)
  ∀α. α → α
```

**Result**: `λx. x : ∀α. α → α` ✓

### Worked Example 2: Const Function

**Infer type of** `λx. λy. x`

```
Step 1: W-Abs (outer lambda)
  α fresh for x
  Γ₁ = {x : α}
  Need to infer: Γ₁ ⊢ λy. x : ?

Step 2: W-Abs (inner lambda)
  β fresh for y
  Γ₂ = {x : α, y : β}
  Need to infer: Γ₂ ⊢ x : ?

Step 3: W-Var (body)
  Γ₂ ⊢ x : α ⇝ []
  (Look up x, get α)

Step 4: Apply W-Abs (inner)
  Inner result: β → α ⇝ []

Step 5: Apply W-Abs (outer)
  Outer result: α → (β → α) ⇝ []

Step 6: Generalize
  ∀α β. α → β → α
```

**Result**: `λx. λy. x : ∀α β. α → β → α` ✓

### Worked Example 3: Application

**Infer type of** `(λx. x) true`

```
Step 1: W-App
  Need to infer types of function and argument

Step 2: Infer function type (λx. x)
  From previous example: α → α ⇝ []
  S₁ = []

Step 3: Infer argument type (true)
  true : Bool ⇝ []
  S₂ = []

Step 4: Unify
  Function type: α → α
  Need to unify: α → α with Bool → β (β fresh result type)

  S₃ = unify(α → α, Bool → β)
     = unify(α, Bool) ∘ unify(α, β)
     = [α ↦ Bool, β ↦ Bool]

Step 5: Result
  S₃(β) = Bool
```

**Result**: `(λx. x) true : Bool` ✓

### Worked Example 4: Twice Function

**Infer type of** `λf. λx. f (f x)`

```
Step 1: W-Abs (outer lambda - f)
  α fresh for f
  Γ₁ = {f : α}

Step 2: W-Abs (inner lambda - x)
  β fresh for x
  Γ₂ = {f : α, x : β}

Step 3: Infer type of body: f (f x)
  This is two applications!

Step 4: Inner application (f x)
  W-Var: f : α
  W-Var: x : β
  W-App: unify(α, β → γ)  (γ fresh)
    S₁ = [α ↦ β → γ]
  Inner result: γ

Step 5: Outer application f (...)
  W-Var: f : S₁(α) = β → γ
  Argument: γ
  W-App: unify(β → γ, γ → δ)  (δ fresh)
    unify(β, γ) = [β ↦ γ]
    S₂ = [β ↦ γ, γ ↦ δ]... Wait!

Let me redo this carefully:
  unify(β → γ, γ → δ):
    unify(β, γ) → S_a = [β ↦ γ]
    unify(S_a(γ), S_a(δ)) = unify(γ, δ) → S_b = [γ ↦ δ]
  S₂ = [β ↦ δ, γ ↦ δ]

  Outer result: δ

Step 6: Apply S₂ to everything
  f : S₂(α) = S₂(β → γ) = δ → δ
  x : S₂(β) = δ
  body : δ

Step 7: Build up the type
  Inner lambda: δ → δ
  Outer lambda: (δ → δ) → δ → δ

Step 8: Generalize
  ∀δ. (δ → δ) → δ → δ
  Or renaming: ∀α. (α → α) → α → α
```

**Result**: `λf. λx. f (f x) : ∀α. (α → α) → α → α` ✓

The function takes a function from α to α, and can apply it twice!

---

## Part 6: Let-Polymorphism - The Key to Power

### Why Is Let Special?

This is the heart of Hindley-Milner. Let's see the difference:

**With let** (WORKS):
```
let id = λx. x in (id true, id 0)
```

**Without let** (FAILS):
```
(λid. (id true, id 0)) (λx. x)
```

Why the difference?

### Let Generalizes, Lambda Doesn't

**Let binding**:
```
let id = λx. x in ...

Step 1: Infer type of λx. x → α → α
Step 2: GENERALIZE → ∀α. α → α
Step 3: Add to environment: id : ∀α. α → α
Step 4: Each use of id gets fresh instantiation!
```

**Lambda binding**:
```
(λid. ...) (λx. x)

Step 1: Infer type of λx. x → β → β
Step 2: NO GENERALIZATION
Step 3: id has monomorphic type β → β
Step 4: All uses must use the SAME β!
```

### Complete Let-Polymorphism Example

**Infer type of**: `let id = λx. x in (id true, id 0)`

```
Step 1: W-Let
  Need to infer type of λx. x

Step 2: Infer bound expression
  λx. x : α → α ⇝ []

Step 3: GENERALIZE
  σ = gen(∅, α → α) = ∀α. α → α

Step 4: Extend environment
  Γ' = {id : ∀α. α → α}

Step 5: Infer body (id true, id 0)
  This is a pair, so we need both components

Step 6: Infer (id true)
  W-Var: instantiate(∀α. α → α) = β → β  (β fresh)
  W-App: unify(β → β, Bool → γ)
    → [β ↦ Bool, γ ↦ Bool]
  Result: Bool

Step 7: Infer (id 0)
  W-Var: instantiate(∀α. α → α) = δ → δ  (δ fresh, different from β!)
  W-App: unify(δ → δ, Nat → ε)
    → [δ ↦ Nat, ε ↦ Nat]
  Result: Nat

Step 8: Pair type
  (Bool, Nat) : Bool × Nat
```

**Result**: Works! Type is `Bool × Nat`

### Why Lambda Can't Be Polymorphic

**Attempt**: `(λid. (id true, id 0)) (λx. x)`

```
Step 1: W-App
  Need types of function and argument

Step 2: Infer function (λid. ...)
  W-Abs: id has monomorphic type α (fresh)
  Γ = {id : α}  (NOT a type scheme!)

  Infer body (id true, id 0):
    id true: unify(α, Bool → β) → α = Bool → β
    id 0: unify(α, Nat → γ) → α = Nat → γ

    CONFLICT! α = Bool → β AND α = Nat → γ
    unify(Bool → β, Nat → γ) → FAIL

ERROR: Cannot unify Bool and Nat
```

### The Rule

**Only let-bound variables are polymorphic.**

Lambda-bound variables are monomorphic.

### Why This Design?

Two reasons:

1. **Decidability**: Allowing polymorphic lambdas requires System F, where type inference is undecidable.

2. **Implementation**: Let-bindings are second-class (can't be passed around), so we can safely generalize them.

---

## Part 7: Principal Types - The Best Answer

### What Is a Principal Type?

A **principal type** is the "most general" type for a term.

**Example**: `λx. x`
- Could have type `Nat → Nat` ✓
- Could have type `Bool → Bool` ✓
- Could have type `α → α` ✓ (PRINCIPAL!)

`α → α` is principal because it's more general - you can instantiate it to get any of the others.

### The Principal Types Theorem

**Theorem**: If a term has a type, it has a unique principal type (up to renaming of variables).

**Consequence**: Algorithm W always finds the most general type!

**Example**:
```
Term: λf. λx. f x

Could type as:
- (Nat → Nat) → Nat → Nat ✓
- (Bool → Bool) → Bool → Bool ✓
- (α → β) → α → β ✓ (PRINCIPAL!)

Algorithm W finds: ∀α β. (α → β) → α → β
```

### Why Principal Types Matter

1. **Uniqueness**: No arbitrary choices - there's always a "best" type
2. **Generality**: The inferred type works in the most contexts
3. **Documentation**: The principal type tells you the most about the function

### Practice: Finding Principal Types

For each term, what's the principal type?

1. `λx. λy. x`
2. `λf. λg. λx. f (g x)`
3. `λx. (x, x)`

<details>
<summary>Solutions</summary>

1. `∀α β. α → β → α`
2. `∀α β γ. (β → γ) → (α → β) → α → γ`
3. `∀α. α → α × α`

</details>

---

## Part 8: Complete Examples

### Example 1: S Combinator

**Term**: `λx. λy. λz. x z (y z)`

**Goal**: Infer the principal type

```
Step 1: W-Abs (x)
  α fresh for x
  Γ₁ = {x : α}

Step 2: W-Abs (y)
  β fresh for y
  Γ₂ = {x : α, y : β}

Step 3: W-Abs (z)
  γ fresh for z
  Γ₃ = {x : α, y : β, z : γ}

Step 4: Infer body: x z (y z)
  This is: (x z) applied to (y z)

Step 5: Infer (y z)
  y : β
  z : γ
  unify(β, γ → δ)  (δ fresh)
  S₁ = [β ↦ γ → δ]
  Result: δ

Step 6: Infer (x z)
  x : S₁(α) = α
  z : S₁(γ) = γ
  unify(α, γ → ε)  (ε fresh)
  S₂ = [α ↦ γ → ε]
  Result: ε

Step 7: Apply (x z) to (y z)
  Function: ε
  Argument: S₂(δ) = δ
  unify(ε, δ → ζ)  (ζ fresh)
  S₃ = [ε ↦ δ → ζ]
  Result: ζ

Step 8: Compose all substitutions
  S = S₃ ∘ S₂ ∘ S₁

  α ↦ γ → (δ → ζ)
  β ↦ γ → δ
  Final result type: ζ

Step 9: Build up function types
  z : γ
  y : γ → δ
  x : γ → δ → ζ

  Type: (γ → δ → ζ) → (γ → δ) → γ → ζ

Step 10: Generalize
  ∀α β γ. (α → β → γ) → (α → β) → α → γ
```

**Result**: The famous S combinator type!

### Example 2: List Map (Conceptual)

**Term**: `λf. λlist. ...` (using fix for recursion)

**Expected Type**: `(α → β) → List α → List β`

The key insights:
- `f` transforms elements: `α → β`
- Input list has type `List α`
- Output list has type `List β`
- The type variables α and β can be different!

This is polymorphism in action: map works for any element types.

---

## Part 9: HM vs STLC vs System F

### The Comparison

| Feature | STLC (Ch 2) | Hindley-Milner (Ch 4) | System F (Ch 5) |
|---------|-------------|----------------------|-----------------|
| Type annotations | Required | None! | Required for polymorphism |
| Polymorphism | None | Let-polymorphism | Full first-class |
| Type inference | Trivial | Algorithm W | Undecidable |
| Expressiveness | Low | Medium | High |
| Decidability | Decidable | Decidable | Decidable (checking) |

### What HM Gives Up

**Limitation 1**: No first-class polymorphism
```
-- Want to write:
λf. (f 0, f true)    -- ERROR: f must be monomorphic

-- Must use let:
let f = λx. x in (f 0, f true)    -- OK
```

**Limitation 2**: No higher-rank types
```
-- Want: function taking a polymorphic function
applyToBoth : (∀α. α → α) → Bool × Nat
applyToBoth f = (f true, f 0)

-- ERROR: Can't express this in HM
```

**Limitation 3**: No type-level computation

These limitations are addressed in System F and beyond!

---

## Part 10: Metatheory

### Soundness

**Theorem (Soundness)**: If Algorithm W succeeds with `W(Γ, t) = (S, τ)`, then the term is typeable in STLC with explicit annotations.

**Meaning**: Inferred types are correct - they match what you'd get with explicit types.

### Completeness

**Theorem (Completeness)**: If a term is typeable in STLC, then Algorithm W succeeds and finds a more general type.

**Meaning**: We don't lose any well-typed programs.

### Decidability

**Theorem (Decidability)**: Type inference for Hindley-Milner is decidable.

**Complexity**:
- Worst case: DEXPTIME-complete
- Practice: Nearly linear for real programs

### Termination

**Theorem (Strong Normalization)**: All well-typed HM programs terminate.

**Why**: HM is a restriction of STLC, which has strong normalization.

**Consequence**: Still can't write general recursion without `fix`.

---

## Summary

### Key Takeaways

1. **Type variables** represent "any type" - enabling polymorphism
2. **Substitutions** are solutions to type equations
3. **Unification** solves type equations (with occurs check!)
4. **Algorithm W** infers types by generating and solving constraints
5. **Let-polymorphism** generalizes let-bound variables, not lambdas
6. **Principal types** ensure unique, most general types

### The Magic Formula

```
Type Inference = Constraints + Unification + Let-Generalization
```

### What Makes HM Special

- Write code without annotations
- Get complete type safety
- Decidable and efficient
- Principal types guarantee "best" types
- Foundation for ML, OCaml, Haskell, F#

### Next Steps

Ready to move on? You should be able to:
- Perform type inference by hand
- Apply unification to solve type equations
- Explain let-polymorphism
- Understand why certain programs don't type check
- Appreciate the power and limitations of HM

Next up: **System F** - what happens when we want more polymorphism!
