# Chapter 9: Subtyping - Cheat Sheet

## Core Concept

**Subtyping**: `S <: T` means "S is a subtype of T" - any value of type S can be used where T is expected.

```
Subsumption Rule:
  Γ ⊢ t : S    S <: T
─────────────────────── (T-Sub)
       Γ ⊢ t : T
```

## Types

```
τ ::= Bool                    -- Boolean type
    | Nat                     -- Natural numbers
    | τ₁ → τ₂                 -- Function type
    | Top                     -- Top type (⊤)
    | Bot                     -- Bottom type (⊥)
    | {l₁: τ₁, ..., lₙ: τₙ}   -- Record type
```

## Subtyping Rules Quick Reference

### Structural Rules

```
─────────── (S-Refl)
  τ <: τ

 τ₁ <: τ₂    τ₂ <: τ₃
─────────────────────── (S-Trans)
       τ₁ <: τ₃
```

### Top and Bottom

```
─────────── (S-Top)     Every type is a subtype of Top
  τ <: Top

─────────── (S-Bot)     Bot is a subtype of every type
  Bot <: τ
```

### Function Subtyping (CONTRAVARIANT/COVARIANT)

```
  σ₁ <: τ₁    τ₂ <: σ₂
─────────────────────── (S-Arrow)
  τ₁ → τ₂ <: σ₁ → σ₂

Key: Arguments are CONTRAVARIANT (←), Results are COVARIANT (→)
```

### Record Subtyping

**Width** (more fields = subtype):
```
─────────────────────────────────────────── (S-RcdWidth)
  {l₁:τ₁, ..., lₙ:τₙ, k:σ} <: {l₁:τ₁, ..., lₙ:τₙ}
```

**Depth** (field types are subtypes):
```
        τᵢ <: σᵢ  for all i
─────────────────────────────── (S-RcdDepth)
  {lᵢ:τᵢ} <: {lᵢ:σᵢ}
```

## Variance Table

| Position | Variance | Rule |
|----------|----------|------|
| Return type | Covariant (+) | If `S <: T`, then `A → S <: A → T` |
| Argument type | Contravariant (-) | If `S <: T`, then `T → A <: S → A` |
| Record field | Covariant (+) | If `S <: T`, then `{f: S} <: {f: T}` |
| Mutable ref | Invariant (±) | Neither covariant nor contravariant |

### Variance Composition

```
Position               Variance
────────────────────────────────
X in Bool → X              +    (covariant)
X in X → Bool              -    (contravariant)
X in (X → A) → B           +    (- × - = +)
X in (A → X) → B           -    (+ × - = -)
X in A → (X → B)           -    (+ × - = -)
X in A → (B → X)           +    (+ × + = +)
```

## Join and Meet

### Join (⊔) - Least Upper Bound

```
τ₁ ⊔ τ₂ = τ₂        if τ₁ <: τ₂
τ₁ ⊔ τ₂ = τ₁        if τ₂ <: τ₁
Bot ⊔ τ = τ
Top ⊔ τ = Top
Nat ⊔ Bool = Top    (no common supertype except Top)

(σ₁ → σ₂) ⊔ (τ₁ → τ₂) = (σ₁ ⊓ τ₁) → (σ₂ ⊔ τ₂)

{lᵢ:σᵢ} ⊔ {lⱼ:τⱼ} = {lₖ:(σₖ ⊔ τₖ)}  where k ∈ (labels(i) ∩ labels(j))
```

### Meet (⊓) - Greatest Lower Bound

```
τ₁ ⊓ τ₂ = τ₁        if τ₁ <: τ₂
τ₁ ⊓ τ₂ = τ₂        if τ₂ <: τ₁
Top ⊓ τ = τ
Bot ⊓ τ = Bot
Nat ⊓ Bool = Bot    (no common subtype except Bot)

(σ₁ → σ₂) ⊓ (τ₁ → τ₂) = (σ₁ ⊔ τ₁) → (σ₂ ⊓ τ₂)

{lᵢ:σᵢ} ⊓ {lⱼ:τⱼ} = {lₖ:(σₖ ⊓ τₖ)}  where k ∈ (labels(i) ∪ labels(j))
```

## Common Patterns

### Width Subtyping

```haskell
{x: Nat, y: Bool, z: Top} <: {x: Nat, y: Bool} <: {x: Nat}

-- More fields = more specific = subtype
```

### Function Subtyping Examples

```haskell
Top → Bot <: Nat → Bool
-- Because: Nat <: Top (contravariant arg)
--          Bot <: Bool (covariant result)

(Bool → Nat) → String <: (Nat → Bool) → String  -- ERROR!
-- Need: Nat → Bool <: Bool → Nat
-- Need: Bool <: Nat (contravariant) - FAILS
```

### Ascription (Upcasting Only)

```haskell
true as Top                        -- OK: Bool <: Top
{x = 0, y = true} as {x: Nat}      -- OK: width subtyping
(\x:Top. 0) as (Bool → Nat)        -- OK: Top → Nat <: Bool → Nat

0 as Bool                          -- ERROR: Nat ⊀ Bool
(0 as {x: Nat})                    -- ERROR: Nat ⊀ {x: Nat}
```

## Type Checking with Subtyping

### Modified Application Rule

```
  Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : σ    σ <: τ₁
──────────────────────────────────────────── (T-App)
                 Γ ⊢ t₁ t₂ : τ₂
```

### Conditional with Join

```
  Γ ⊢ t₁ : Bool    Γ ⊢ t₂ : τ₂    Γ ⊢ t₃ : τ₃
────────────────────────────────────────────── (T-If)
        Γ ⊢ if t₁ then t₂ else t₃ : τ₂ ⊔ τ₃
```

### Ascription

```
  Γ ⊢ t : S    S <: T
─────────────────────── (T-Ascribe)
    Γ ⊢ (t as T) : T
```

## The Subtype Lattice

```
                    Top
                 /   |   \
               /     |     \
             /       |       \
          Bool      Nat    {records}
             \       |       /
               \     |     /
                 \   |   /
                    Bot
```

## Quick Decision Tree

**To check `S <: T`:**

1. If `S == T` → ✓ (reflexivity)
2. If `T == Top` → ✓ (Top is supertype of all)
3. If `S == Bot` → ✓ (Bot is subtype of all)
4. If both are functions `S₁ → S₂` and `T₁ → T₂`:
   - Check `T₁ <: S₁` (contravariant)
   - Check `S₂ <: T₂` (covariant)
5. If both are records:
   - All fields in T must exist in S
   - Each field type in S must be subtype of corresponding field in T
6. Otherwise → ✗

## Remember

### ✓ Do
- Width subtyping: more fields = subtype
- Function arguments: contravariant (flip direction)
- Function results: covariant (same direction)
- Join for if-then-else branches
- Use Top when you don't care about type
- Use Bot for unreachable code

### ✗ Avoid
- Confusing width subtyping direction
- Forgetting function contravariance
- Trying to downcast with ascription
- Expecting join to keep all fields (only common)
- Making mutable refs covariant (they're invariant!)

## Examples

### Example 1: Width Subtyping
```
f : {x: Nat} → Nat
f = λp:{x: Nat}. p.x

f {x = 5, y = true}    -- OK: {x: Nat, y: Bool} <: {x: Nat}
```

### Example 2: Contravariance
```
g : (Top → Nat) → Nat
g = λh:(Top → Nat). h true

f : Top → Nat
f = λx:Top. 0

g f    -- OK: Top → Nat <: Bool → Nat (because Bool <: Top)
```

### Example 3: Join
```
if condition
  then {x = 0, y = true}
  else {x = 5, z = false}
-- Type: {x: Nat}  (only common field)
```

## REPL Commands

```bash
:type <expr>        # Show type of expression
:subtype T1 T2      # Check if T1 <: T2
:help               # Show help
:quit               # Exit
```

## Algorithmic Subtyping

```haskell
subtype :: Type -> Type -> Bool
subtype t1 t2
  | t1 == t2 = True                    -- Reflexivity
  | TyTop <- t2 = True                 -- Top is supertype
  | TyBot <- t1 = True                 -- Bot is subtype
  | TyArr s1 s2 <- t1
  , TyArr u1 u2 <- t2
  = subtype u1 s1 && subtype s2 u2     -- Contravariant/Covariant
  | TyRecord f1 <- t1
  , TyRecord f2 <- t2
  = all (\(l, t) -> case Map.lookup l f1 of
           Just t' -> subtype t' t
           Nothing -> False) (Map.toList f2)
  | otherwise = False
```

## Real-World Applications

### TypeScript Structural Typing
```typescript
interface Point { x: number; y: number }
interface ColoredPoint { x: number; y: number; color: string }
// ColoredPoint <: Point (width subtyping)
```

### Scala Variance Annotations
```scala
class List[+A]              // Covariant
class Function1[-A, +B]     // Contravariant in A, Covariant in B
```

### Java/C# (Broken) Array Covariance
```java
String[] strings = new String[1];
Object[] objects = strings;  // Allowed but unsound
objects[0] = 42;             // Runtime error!
```

## Next Steps

After mastering subtyping:
- **Chapter 10**: Linear types (resource tracking)
- **Bounded quantification**: `∀α <: T. τ`
- **Intersection/Union types**: `A ∧ B`, `A ∨ B`

## Further Reading

- **Pierce, TAPL**: Chapters 15-17 (comprehensive treatment)
- **Cardelli (1988)**: "A Semantics of Multiple Inheritance"
- **Liskov (1988)**: "Data Abstraction and Hierarchy" (LSP)
