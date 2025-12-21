# Chapter 9: Subtyping

This chapter introduces **subtyping**, a fundamental concept that allows more flexible type systems by establishing relationships between types. Subtyping enables **implicit upcasting**: a value of type `S` can be used wherever a value of type `T` is expected, provided `S` is a subtype of `T` (written `S <: T`).

## Overview

Subtyping adds expressiveness to type systems by allowing:

1. **Subsumption**: Using a more specific type where a more general type is expected
2. **Record width subtyping**: Records with more fields are subtypes of records with fewer fields
3. **Record depth subtyping**: Records with more specific field types are subtypes
4. **Function subtyping**: Contravariant in argument, covariant in result

## Types

```
τ ::= Bool                    -- Boolean type
    | Nat                     -- Natural number type
    | τ₁ → τ₂                 -- Function type
    | Top                     -- Top type (supertype of everything)
    | Bot                     -- Bottom type (subtype of everything)
    | {l₁: τ₁, ..., lₙ: τₙ}   -- Record type
```

### Top and Bottom Types

- **Top** (`⊤`): The supertype of all types. Every type is a subtype of Top.
- **Bot** (`⊥`): The subtype of all types. Bot is a subtype of every type.

These types form the boundaries of the subtype lattice:
```
        Top
       / | \
     Bool Nat {x:τ}...
       \ | /
        Bot
```

## Terms

```
t ::= x                       -- Variable
    | λx:τ. t                 -- Abstraction
    | t₁ t₂                   -- Application
    | true | false            -- Booleans
    | if t₁ then t₂ else t₃   -- Conditional
    | 0 | succ t | pred t     -- Natural numbers
    | iszero t                -- Zero test
    | {l₁ = t₁, ..., lₙ = tₙ} -- Record
    | t.l                     -- Projection
    | t as τ                  -- Ascription
```

## Subtyping Rules

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
─────────── (S-Top)
  τ <: Top

─────────── (S-Bot)
  Bot <: τ
```

### Function Subtyping

Functions are **contravariant** in their argument type and **covariant** in their result type:

```
  σ₁ <: τ₁    τ₂ <: σ₂
─────────────────────── (S-Arrow)
  τ₁ → τ₂ <: σ₁ → σ₂
```

**Key insight**: A function `f : A → B` can be used where `f : A' → B'` is expected if:
- `A' <: A` (we can accept more general arguments)
- `B <: B'` (we return more specific results)

### Record Subtyping

**Width subtyping**: Records with more fields are subtypes.

```
─────────────────────────────────────────── (S-RcdWidth)
  {l₁:τ₁, ..., lₙ:τₙ, lₙ₊₁:τₙ₊₁} <: {l₁:τ₁, ..., lₙ:τₙ}
```

**Depth subtyping**: Field types can be subtypes.

```
        τᵢ <: σᵢ  for all i
─────────────────────────────── (S-RcdDepth)
  {lᵢ:τᵢ} <: {lᵢ:σᵢ}
```

**Permutation**: Field order doesn't matter (handled by using Map).

## Typing Rules with Subsumption

The key addition is the **subsumption rule**:

```
  Γ ⊢ t : S    S <: T
─────────────────────── (T-Sub)
       Γ ⊢ t : T
```

This rule states that if a term has type `S` and `S` is a subtype of `T`, then the term also has type `T`.

### Modified Application Rule

```
  Γ ⊢ t₁ : τ₁ → τ₂    Γ ⊢ t₂ : σ    σ <: τ₁
──────────────────────────────────────────── (T-App)
                 Γ ⊢ t₁ t₂ : τ₂
```

### Ascription

```
  Γ ⊢ t : S    S <: T
─────────────────────── (T-Ascribe)
    Γ ⊢ (t as T) : T
```

### Conditionals with Join

For if-then-else, we need the **least upper bound** (join) of the branch types:

```
  Γ ⊢ t₁ : Bool    Γ ⊢ t₂ : τ₂    Γ ⊢ t₃ : τ₃    τ = τ₂ ⊔ τ₃
────────────────────────────────────────────────────────────── (T-If)
                  Γ ⊢ if t₁ then t₂ else t₃ : τ
```

## Join and Meet

The **join** (`⊔`) computes the least upper bound of two types:
- Used for if-then-else branches
- `τ₁ ⊔ τ₂` is the smallest type that is a supertype of both

The **meet** (`⊓`) computes the greatest lower bound:
- Used for function argument positions
- `τ₁ ⊓ τ₂` is the largest type that is a subtype of both

### Join Rules

```
τ₁ ⊔ τ₂ = τ₂        if τ₁ <: τ₂
τ₁ ⊔ τ₂ = τ₁        if τ₂ <: τ₁
Bot ⊔ τ = τ
τ ⊔ Bot = τ
Top ⊔ τ = Top

(σ₁ → σ₂) ⊔ (τ₁ → τ₂) = (σ₁ ⊓ τ₁) → (σ₂ ⊔ τ₂)

{lᵢ:σᵢ} ⊔ {lⱼ:τⱼ} = {lₖ:(σₖ ⊔ τₖ)}  where k ∈ i ∩ j
```

### Meet Rules

```
τ₁ ⊓ τ₂ = τ₁        if τ₁ <: τ₂
τ₁ ⊓ τ₂ = τ₂        if τ₂ <: τ₁
Top ⊓ τ = τ
τ ⊓ Top = τ
Bot ⊓ τ = Bot

(σ₁ → σ₂) ⊓ (τ₁ → τ₂) = (σ₁ ⊔ τ₁) → (σ₂ ⊓ τ₂)

{lᵢ:σᵢ} ⊓ {lⱼ:τⱼ} = {lₖ:(σₖ ⊓ τₖ) | k ∈ i ∪ j}
```

## Variance

**Variance** describes how subtyping of a type constructor relates to subtyping of its arguments:

- **Covariant** (+): If `S <: T`, then `F[S] <: F[T]`
  - Examples: Return types, record fields

- **Contravariant** (-): If `S <: T`, then `F[T] <: F[S]`
  - Examples: Function argument types

- **Invariant** (±): Neither covariant nor contravariant
  - Examples: Mutable references

### Position Analysis

```
X → Bool           X is in contravariant position (-)
Bool → X           X is in covariant position (+)
(X → Bool) → Nat   X is in covariant position (- × - = +)
(Bool → X) → Nat   X is in contravariant position (+ × - = -)
```

## Examples

### Width Subtyping

```haskell
-- Point with x, y coordinates
point : {x: Nat, y: Nat}
point = {x = 0, y = 0}

-- Colored point with additional color field
coloredPoint : {x: Nat, y: Nat, color: Bool}
coloredPoint = {x = 0, y = 0, color = true}

-- Function accepting any point
getX : {x: Nat} -> Nat
getX = λp:{x: Nat}. p.x

-- Works on both:
getX point        -- OK: {x: Nat, y: Nat} <: {x: Nat}
getX coloredPoint -- OK: {x: Nat, y: Nat, color: Bool} <: {x: Nat}
```

### Function Subtyping

```haskell
-- A function accepting Top returns Nat
f : Top -> Nat
f = λx:Top. 0

-- Can be used where Bool -> Nat is expected
-- Because Top -> Nat <: Bool -> Nat (contravariance)
g : (Bool -> Nat) -> Nat
g = λh:(Bool -> Nat). h true

g f  -- Type checks! f : Top -> Nat <: Bool -> Nat
```

### Ascription

```haskell
-- Explicit upcast using ascription
true as Top        -- OK: Bool <: Top
{x = 0} as {x: Top} -- OK: {x: Nat} <: {x: Top} (depth)
{x = 0, y = true} as {x: Nat}  -- OK: width subtyping
```

## Metatheory

### Type Safety

**Theorem (Progress)**: If `⊢ t : τ`, then either `t` is a value or there exists `t'` such that `t → t'`.

**Theorem (Preservation)**: If `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`.

### Subtyping Properties

**Theorem (Reflexivity)**: `τ <: τ` for all types `τ`.

**Theorem (Transitivity)**: If `τ₁ <: τ₂` and `τ₂ <: τ₃`, then `τ₁ <: τ₃`.

**Theorem (Antisymmetry)**: If `τ₁ <: τ₂` and `τ₂ <: τ₁`, then `τ₁ = τ₂` (up to record field reordering).

### Join/Meet Properties

**Theorem (Join is LUB)**:
1. `τ₁ <: τ₁ ⊔ τ₂` and `τ₂ <: τ₁ ⊔ τ₂`
2. If `τ₁ <: σ` and `τ₂ <: σ`, then `τ₁ ⊔ τ₂ <: σ`

**Theorem (Meet is GLB)**:
1. `τ₁ ⊓ τ₂ <: τ₁` and `τ₁ ⊓ τ₂ <: τ₂`
2. If `σ <: τ₁` and `σ <: τ₂`, then `σ <: τ₁ ⊓ τ₂`

## Algorithmic Subtyping

The implementation uses a syntax-directed algorithm that checks subtyping structurally:

```haskell
subtype :: Type -> Type -> Bool
subtype t1 t2
  | t1 == t2 = True           -- Reflexivity
  | TyTop <- t2 = True        -- Top is supertype
  | TyBot <- t1 = True        -- Bot is subtype
  | TyArr s1 s2 <- t1
  , TyArr u1 u2 <- t2
  = subtype u1 s1 && subtype s2 u2  -- Function (contra/co)
  | TyRecord f1 <- t1
  , TyRecord f2 <- t2
  = recordSubtype f1 f2       -- Record subtyping
  | otherwise = False
```

This algorithm is:
- **Sound**: If it returns True, the subtyping relation holds
- **Complete**: If the relation holds, it returns True
- **Terminating**: Structural recursion on types

## Real-World Applications

### Object-Oriented Programming

Subtyping models class inheritance:
- A subclass has at least the methods of its superclass
- Method arguments are contravariant, returns are covariant
- This is why Java/C# arrays are broken (they're covariant but mutable)

### TypeScript/Flow

Modern JavaScript type systems use structural subtyping:
```typescript
interface Point { x: number; y: number }
interface ColoredPoint { x: number; y: number; color: string }

// ColoredPoint is a structural subtype of Point
function getX(p: Point): number { return p.x; }
getX({ x: 0, y: 0, color: "red" }); // OK
```

### Scala

Scala uses variance annotations:
```scala
class List[+A]     // Covariant: List[Dog] <: List[Animal]
class Function[-A, +B]  // Contravariant in A, covariant in B
```

## File Structure

```
chapter-09-subtyping/
├── src/
│   ├── Syntax.hs      -- Types and terms with Top, Bot, records
│   ├── TypeCheck.hs   -- Subtyping algorithm, join/meet, type checking
│   ├── Eval.hs        -- Call-by-value evaluation
│   ├── Parser.hs      -- Megaparsec parser
│   └── Pretty.hs      -- Pretty printer
├── app/
│   └── Main.hs        -- REPL
├── test/
│   └── Spec.hs        -- 74 tests
├── exercises/
│   └── EXERCISES.md   -- 10 exercises + challenges
├── package.yaml
├── stack.yaml
└── README.md          -- This file
```

## Building and Testing

```bash
cd chapter-09-subtyping
stack build
stack test   # 74 tests
stack exec subtyping-repl  # Interactive REPL
```

## REPL Commands

```
subtype> :help              -- Show help
subtype> :type <expr>       -- Show type of expression
subtype> :subtype T1 T2     -- Check if T1 <: T2
subtype> :quit              -- Exit
```

## References

### Primary Sources

1. **Cardelli, L.** (1988). "A Semantics of Multiple Inheritance". *Information and Computation*, 76(2-3), 138-164.
   - Foundational paper on record subtyping and inheritance

2. **Cardelli, L. & Wegner, P.** (1985). "On Understanding Types, Data Abstraction, and Polymorphism". *Computing Surveys*, 17(4), 471-522.
   - Classic survey connecting subtyping to OOP concepts

3. **Pierce, B.C.** (2002). *Types and Programming Languages*, Chapters 15-17.
   - Comprehensive treatment of subtyping theory

### Extended Reading

4. **Cardelli, L.** (1984). "A Semantics of Multiple Inheritance". *Semantics of Data Types*.
   - Original bounded quantification paper

5. **Pierce, B.C. & Turner, D.N.** (2000). "Local Type Inference". *ACM TOPLAS*, 22(1), 1-44.
   - Bidirectional type checking with subtyping

6. **Liskov, B.** (1988). "Keynote Address - Data Abstraction and Hierarchy". *OOPSLA '87 Addendum*.
   - The "Liskov Substitution Principle"

### Related Systems

7. **Amadio, R. & Cardelli, L.** (1993). "Subtyping Recursive Types". *ACM TOPLAS*, 15(4), 575-631.
   - Recursive types with subtyping

8. **Hosoya, H. & Pierce, B.C.** (2003). "XDuce: A Statically Typed XML Processing Language". *ACM TWEB*.
   - Regular expression types with subtyping

---

**Tests**: 74/74 passing | **Exercises**: 10 problems + 3 challenges
