# Chapter 4: Visual Aids

## Algorithm W Flowchart

```
┌─────────────────────────────────────────────────────────────┐
│                     ALGORITHM W                              │
│                   infer(Γ, term)                            │
└─────────────────────────────────────────────────────────────┘
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
        ▼                  ▼                  ▼
   ┌─────────┐        ┌─────────┐        ┌─────────┐
   │   Var   │        │   Lam   │        │   App   │
   └────┬────┘        └────┬────┘        └────┬────┘
        │                  │                  │
        ▼                  ▼                  ▼
   lookup σ in       generate fresh      infer both
   Γ, instantiate       α for x          sides, unify
        │                  │                  │
        ▼                  ▼                  ▼
  return (τ, [])     return (α→τ, S)    return (β, S)

                           │
                           ▼
                    ┌─────────────┐
                    │     Let     │
                    └──────┬──────┘
                           │
                           ▼
                    infer t₁, generalize
                    to σ, infer t₂ with
                    x : σ in context
```

---

## Unification Algorithm

### Robinson's Unification

```
unify(τ₁, τ₂)
        │
   ┌────┴────────────────────────────┐
   │                                 │
   ▼                                 ▼
τ₁ = α (type var)              τ₁, τ₂ both concrete
   │                                 │
   ▼                                 │
┌────────────────┐            ┌──────┴──────┐
│ α ∈ FV(τ₂)?    │            │  Match?     │
└───────┬────────┘            └──────┬──────┘
     │      │                    │       │
   YES      NO                 YES       NO
     │      │                    │       │
     ▼      ▼                    ▼       ▼
  FAIL   [α ↦ τ₂]            recurse   FAIL
 (occurs              on parts
  check)

Example: unify(α → β, Nat → Bool)

         α → β    Nat → Bool
           │          │
           ▼          ▼
    unify(α, Nat) ∪ unify(β, Bool)
           │              │
           ▼              ▼
       [α ↦ Nat]     [β ↦ Bool]
           │              │
           └──────┬───────┘
                  ▼
          [α ↦ Nat, β ↦ Bool]
```

### Occurs Check Failure

```
unify(α, α → Nat)

    α     α → Nat
    │         │
    └────┬────┘
         │
    Does α occur in (α → Nat)?
         │
        YES!
         │
         ▼
    ┌─────────────────────────────────┐
    │ FAIL: Cannot create infinite   │
    │ type α = α → Nat               │
    │                                │
    │ Would expand to:               │
    │ α = α → Nat                    │
    │   = (α → Nat) → Nat            │
    │   = ((α → Nat) → Nat) → Nat    │
    │   = ...forever                 │
    └─────────────────────────────────┘
```

---

## Let vs Lambda Polymorphism

### Let Allows Multiple Uses at Different Types

```
let id = λx. x in (id 5, id true)

Step 1: Infer λx. x
        ┌────────────────┐
        │  λx. x : α → α │
        └────────────────┘

Step 2: Generalize (α not in Γ)
        ┌─────────────────────┐
        │  id : ∀α. α → α     │  ← POLYMORPHIC!
        └─────────────────────┘

Step 3: Use id at Nat
        instantiate: β → β (fresh β)
        unify with Nat → γ
        result: id 5 : Nat

Step 4: Use id at Bool
        instantiate: δ → δ (fresh δ, different!)
        unify with Bool → ε
        result: id true : Bool

Final: (Nat, Bool) ✓
```

### Lambda Does NOT Allow This

```
(λid. (id 5, id true)) (λx. x)

Step 1: λid takes parameter
        ┌────────────────┐
        │  id : α        │  ← MONOMORPHIC!
        └────────────────┘

Step 2: Use id at Nat
        unify(α, Nat → β)
        α = Nat → β

Step 3: Use id at Bool
        But α = Nat → β already!
        unify(Nat → β, Bool → γ)
        unify(Nat, Bool)

        ┌─────────────────────┐
        │  FAIL: Nat ≠ Bool   │
        └─────────────────────┘
```

### Visual Comparison

```
LET:                          LAMBDA:
────                          ──────
let id = λx.x in             (λid. ...) (λx.x)
    │                              │
    ▼ generalize                   ▼ no generalization
    ∀α. α → α                      β → β (fixed)
    │                              │
    ├─►instantiate─► γ → γ         ├─► use: γ → γ
    │   (for Nat)                  │   unify with Nat→δ
    │                              │   β = Nat → δ
    │                              │
    └─►instantiate─► δ → δ         └─► use: Nat → δ
        (for Bool, fresh!)             unify with Bool→ε
                                       Nat ≠ Bool ✗
```

---

## Substitution Composition

### Threading Substitutions

```
infer(Γ, t₁ t₂):

    ┌─────────────────────────────────┐
    │ (τ₁, S₁) = infer(Γ, t₁)        │
    └───────────────┬─────────────────┘
                    │
                    ▼ Apply S₁!
    ┌─────────────────────────────────┐
    │ (τ₂, S₂) = infer(S₁(Γ), t₂)    │
    └───────────────┬─────────────────┘
                    │
                    ▼ Apply S₂!
    ┌─────────────────────────────────┐
    │ S₃ = unify(S₂(τ₁), τ₂ → α)     │
    └───────────────┬─────────────────┘
                    │
                    ▼ Compose all
    ┌─────────────────────────────────┐
    │ return (S₃(α), S₃ ∘ S₂ ∘ S₁)   │
    └─────────────────────────────────┘
```

### Composition Order

```
S₁ = [α ↦ Nat]
S₂ = [β ↦ α]

S₂ ∘ S₁ means "apply S₁ first, then S₂"

(S₂ ∘ S₁)(β) = S₂(S₁(β))
             = S₂(β)        (S₁ doesn't affect β)
             = α

(S₂ ∘ S₁)(α) = S₂(S₁(α))
             = S₂(Nat)
             = Nat

Result: S₂ ∘ S₁ = [α ↦ Nat, β ↦ α]

But wait! We need to apply S₁ to the result of S₂:

Correct S₂ ∘ S₁ = [α ↦ Nat, β ↦ Nat]
                            ↑
                     S₁ applied!
```

---

## Generalization

### When to Generalize

```
generalize(Γ, τ):

    Free variables in τ:        FV(τ)
    Free variables in Γ:        FV(Γ)
    Can generalize:             FV(τ) \ FV(Γ)

Example:
    Γ = {f : α → β, x : γ}
    τ = α → δ → ε

    FV(τ) = {α, δ, ε}
    FV(Γ) = {α, β, γ}

    Can generalize: {α, δ, ε} \ {α, β, γ}
                  = {δ, ε}

    Result: ∀δ ε. α → δ → ε
                  ↑
            α stays free (it's in Γ)
```

### Visual

```
Environment Γ:           Type τ:
┌──────────────┐        ┌──────────────┐
│ f : α → β    │        │  α → δ → ε   │
│ x : γ        │        │              │
└──────────────┘        └──────────────┘
       │                       │
       ▼                       ▼
  FV = {α, β, γ}          FV = {α, δ, ε}
       │                       │
       └─────────┬─────────────┘
                 │
            {δ, ε} = {α, δ, ε} - {α, β, γ}
                 │
                 ▼
        Generalize to ∀δ ε. α → δ → ε
```

---

## Instantiation

### Fresh Variables Each Time

```
σ = ∀α β. α → β → α

Use 1:                    Use 2:
instantiate(σ)            instantiate(σ)
     │                         │
     ▼                         ▼
[α ↦ γ₁, β ↦ γ₂]         [α ↦ γ₃, β ↦ γ₄]
     │                         │
     ▼                         ▼
γ₁ → γ₂ → γ₁              γ₃ → γ₄ → γ₃
     │                         │
     │    INDEPENDENT!         │
     └─────────────────────────┘

Different fresh variables each time!
```

---

## Type Inference Example

### Inferring `λf. λx. f (f x)`

```
Step 1: Fresh variables
        f : α
        x : β

Step 2: Infer inner (f x)
        f : α, x : β
        Need: α = β → γ (for application)
        Result: f x : γ
        S₁ = [α ↦ β → γ]

Step 3: Infer outer f (f x)
        f : β → γ    (after S₁)
        f x : γ
        Need: β → γ = γ → δ
        unify(β → γ, γ → δ)
        S₂ = [β ↦ γ, δ ↦ γ]

Step 4: Compose
        S = S₂ ∘ S₁ = [α ↦ γ → γ, β ↦ γ, δ ↦ γ]

Step 5: Build type
        λf. λx. f (f x) : (γ → γ) → γ → γ

Step 6: Generalize
        ∀γ. (γ → γ) → γ → γ

Interpretation: "Apply f twice"
```

---

## Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│              HINDLEY-MILNER TYPE INFERENCE                  │
├─────────────────────────────────────────────────────────────┤
│  TYPE SCHEMES                                               │
│    σ = ∀ᾱ. τ          (polytype)                           │
│    τ = α | τ → τ      (monotype)                           │
│                                                             │
│  KEY OPERATIONS                                             │
│    generalize(Γ, τ) = ∀(FV(τ)\FV(Γ)). τ                    │
│    instantiate(∀ᾱ. τ) = [ᾱ ↦ fresh](τ)                     │
│                                                             │
│  UNIFICATION                                                │
│    unify(α, τ) = [α ↦ τ]  if α ∉ FV(τ)                     │
│    unify(τ₁→τ₂, τ₃→τ₄) = unify(τ₁,τ₃) ∪ unify(τ₂,τ₄)      │
│                                                             │
│  KEY INSIGHT                                                │
│    let generalizes, λ does not!                            │
│                                                             │
│  PRINCIPAL TYPES                                            │
│    Every typeable term has a unique most general type      │
└─────────────────────────────────────────────────────────────┘
```
