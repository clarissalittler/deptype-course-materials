# Chapter 4: Hindley-Milner Type Inference

## Overview

This chapter implements the **Hindley-Milner type inference algorithm**, allowing us to write programs **without type annotations** while maintaining complete type safety. This is the type system used by ML, OCaml, Haskell (basis), and many other functional languages.

**Key Innovation**: Automatic type inference + let-polymorphism

## Major Differences from Chapter 2

| Feature | STLC (Ch 2) | Hindley-Milner (Ch 4) |
|---------|-------------|----------------------|
| Type annotations | Required on λ | Not needed! |
| Polymorphism | None | Let-polymorphism |
| Type checking | Explicit types | Infer types |
| Algorithm | Syntax-directed checking | Unification + generalization |

## Syntax

### Types (Monotypes and Polytypes)

```
τ ::=                    (monotypes)
    α                    type variable
    Bool | Nat           base types
    τ → τ                function type
    τ × τ                product type
    List τ               list type

σ ::= ∀α₁...αₙ. τ        (type schemes / polytypes)
```

### Terms (NO TYPE ANNOTATIONS!)

```
t ::=
    x                    variable
    λx. t                lambda (no type!)
    t t                  application
    let x = t in t       let binding
    true | false         booleans
    if t then t else t   conditional
    0 | succ t | pred t  natural numbers
    (t, t)               pairs
    fst t | snd t        projections
    []                   empty list
    t :: t               cons
```

## Type Inference Algorithm

### Type Substitutions

A substitution `S` maps type variables to types:

```
S = [α₁ ↦ τ₁, ..., αₙ ↦ τₙ]

S(α) = τ  if α ↦ τ ∈ S
S(α) = α  if α ∉ dom(S)
S(τ₁ → τ₂) = S(τ₁) → S(τ₂)
...
```

**Composition**: `S₁ ∘ S₂ = { α ↦ S₁(S₂(α)) | α ∈ dom(S₂) } ∪ { α ↦ S₁(α) | α ∈ dom(S₁) \ dom(S₂) }`

### Unification (Robinson's Algorithm)

**Goal**: Find most general unifier (mgu) of two types.

```
unify(τ, τ) = []
unify(α, τ) = [α ↦ τ]  if α ∉ ftv(τ)  (occurs check!)
unify(τ, α) = [α ↦ τ]  if α ∉ ftv(τ)
unify(τ₁ → τ₂, τ₃ → τ₄) = S₂ ∘ S₁
    where S₁ = unify(τ₁, τ₃)
          S₂ = unify(S₁(τ₂), S₁(τ₄))
unify(τ₁, τ₂) = fail  (otherwise)
```

**Occurs Check**: Prevents infinite types like `α = α → α`.

### Type Schemes and Generalization

**Type Scheme**: `∀α₁...αₙ. τ` quantifies type variables.

**Generalization**: Convert monotype to polytype

```
gen(Γ, τ) = ∀ᾱ. τ  where ᾱ = ftv(τ) \ ftv(Γ)
```

Only generalize variables not free in the environment!

**Instantiation**: Create fresh type variables

```
inst(∀α₁...αₙ. τ) = [α₁ ↦ β₁, ..., αₙ ↦ βₙ](τ)
    where β₁, ..., βₙ are fresh
```

### Algorithm W

**Type Inference Judgment**: `Γ ⊢ t : τ ⇝ S`

Infers type `τ` for term `t` under environment `Γ`, producing substitution `S`.

```
─────────────────────────────────── (W-Var)
Γ, x:σ ⊢ x : inst(σ) ⇝ []


Γ, x:α ⊢ t : τ ⇝ S    (α fresh)
─────────────────────────────────── (W-Abs)
Γ ⊢ λx. t : S(α) → τ ⇝ S


Γ ⊢ t₁ : τ₁ ⇝ S₁
S₁(Γ) ⊢ t₂ : τ₂ ⇝ S₂
S₃ = unify(S₂(τ₁), τ₂ → α)    (α fresh)
──────────────────────────────────── (W-App)
Γ ⊢ t₁ t₂ : S₃(α) ⇝ S₃ ∘ S₂ ∘ S₁


Γ ⊢ t₁ : τ₁ ⇝ S₁
S₁(Γ), x:gen(S₁(Γ), τ₁) ⊢ t₂ : τ₂ ⇝ S₂
──────────────────────────────────── (W-Let)
Γ ⊢ let x = t₁ in t₂ : τ₂ ⇝ S₂ ∘ S₁
```

**Key Insight**: Let-bound variables are **generalized**, lambda-bound variables are **not**.

## Let-Polymorphism

### What Works

```haskell
let id = \x. x in (id true, id 0)
-- id gets type: ∀α. α → α
-- Can use at Bool and Nat!
```

### What Doesn't Work

```haskell
\id. (id true, id 0)
-- FAILS! id is monomorphic in lambda
-- Must pick either Bool → Bool or Nat → Nat
```

**Reason**: Generalizing lambda-bound variables would require **impredicative polymorphism** (System F), which is undecidable for type inference.

### Value Restriction

Many ML implementations restrict let-polymorphism to **syntactic values**:

```haskell
let id = \x. x in ...        -- OK: value
let f = expensive_computation in ...  -- Maybe not generalized!
```

This prevents unsoundness in the presence of effects (references, exceptions).

## Principal Types

**Theorem (Principal Types)**: If `Γ ⊢ t : τ`, then there exists a **principal type** `τ₀` such that:
1. `Γ ⊢ t : τ₀`
2. For any other `τ` such that `Γ ⊢ t : τ`, we have `τ = S(τ₀)` for some substitution `S`.

**Consequence**: Algorithm W always finds the **most general type**.

## Properties

### Soundness and Completeness

**Theorem (Soundness)**: If `W(Γ, t) = (S, τ)`, then `S(Γ) ⊢ t : τ` (using explicit STLC rules).

**Theorem (Completeness)**: If `Γ ⊢ t : τ` in STLC, then `W(Γ, t)` succeeds with a more general type.

### Decidability

**Theorem**: Type inference for Hindley-Milner is **decidable**.

**Complexity**: DEXPTIME-complete in worst case, but polynomial for most practical programs.

### Termination

Like STLC, all well-typed Hindley-Milner programs **terminate** (strong normalization).

## Examples

### Classic Polymorphic Functions

```haskell
-- Identity
id = \x. x
-- Type: ∀α. α → α

-- Const
const = \x. \y. x
-- Type: ∀α β. α → β → α

-- Compose
compose = \f. \g. \x. f (g x)
-- Type: ∀α β γ. (β → γ) → (α → β) → α → γ
```

### Let-Polymorphism in Action

```haskell
-- Works: let-polymorphism
let id = \x. x in
let a = id true in
let b = id 0 in
  (a, b)
-- Type: Bool × Nat

-- Fails: lambda variables are monomorphic
\id. (id true, id 0)
-- Error: Cannot unify Bool and Nat
```

### List Functions

```haskell
-- Map (conceptual - would need fix/recursion)
map = fix (\map. \f. \list.
  if isnil list then []
  else f (head list) :: map f (tail list))
-- Type: ∀α β. (α → β) → List α → List β
```

## Limitations

1. **No First-Class Polymorphism**: Cannot pass polymorphic functions as arguments
   ```haskell
   \f. (f true, f 0)  -- FAILS
   ```

2. **No Higher-Rank Types**: Function arguments must be monomorphic

3. **No Type-Level Computation**: Types are static

These are addressed in System F (Chapter 5) and beyond.

## Implementation

### Project Structure

```
chapter-04-hindley-milner/
├── src/
│   ├── Syntax.hs      -- Terms without type annotations
│   ├── Infer.hs       -- Algorithm W implementation
│   ├── Eval.hs        -- Evaluation
│   ├── Parser.hs      -- Parser (no type annotations!)
│   └── Pretty.hs      -- Pretty printer
└── test/Spec.hs       -- Tests for polymorphism
```

### Key Implementation Details

**Substitution Composition**:
```haskell
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Map.map (applySubst s1) s2 `Map.union` s1
```

**Occurs Check**:
```haskell
bindVar :: TyVar -> Type -> Infer Subst
bindVar a t
  | t == TyVar a = return emptySubst
  | a `Set.member` freeTyVars t = throwError $ OccursCheck a t
  | otherwise = return $ Map.singleton a t
```

**Generalization**:
```haskell
generalize :: TypeEnv -> Type -> TypeScheme
generalize env ty =
  let vars = Set.toList (freeTyVars ty Set.\\ freeTyVarsEnv env)
  in TypeScheme vars ty
```

## Real-World Connections

Hindley-Milner type inference is the secret sauce behind ML, OCaml, Haskell, Rust, and F#. It's why these languages feel magical—you write code without type annotations, yet get complete type safety.

### Where You've Seen This

#### **Haskell**
```haskell
-- No type annotations needed!
identity x = x                  -- Inferred: a -> a
compose f g x = f (g x)         -- Inferred: (b -> c) -> (a -> b) -> a -> c

-- Let-polymorphism in action
let id = \x -> x in (id 5, id True)  -- Works! id is polymorphic
```

#### **OCaml / F#**
```ocaml
(* Type inference everywhere *)
let identity x = x;;            (* val identity : 'a -> 'a *)
let map f lst = ...;;           (* val map : ('a -> 'b) -> 'a list -> 'b list *)

(* Polymorphic let *)
let id = fun x -> x in (id 5, id true)  (* ✓ Works *)
```

#### **Rust**
```rust
// Type inference for local variables
let x = 5;                      // i32 inferred
let v = vec![1, 2, 3];         // Vec<i32> inferred

// Generic functions with inference
fn identity<T>(x: T) -> T { x }
let y = identity(5);            // T = i32 inferred
```

#### **TypeScript (Limited HM)**
```typescript
// Partial type inference
const identity = <T>(x: T) => x;     // Generic parameter needed
const x = identity(5);               // T = number inferred from usage

// But can't infer generic parameters themselves
const map = (f, arr) => arr.map(f);  // Types too general without annotations
```

### The Magic: Let-Polymorphism

#### **Works in HM:**
```ocaml
let id = fun x -> x in
  (id 5, id true)               (* ✓ id : ∀a. a → a *)
```

#### **Doesn't work in STLC:**
```
(λid. (id 5, id true)) (λx. x)  (* ✗ Type error! *)
```

**Why?** Let generalizes, lambda doesn't!

### Key Concept Mappings

| HM Concept | Real-World Feature |
|------------|-------------------|
| **Type inference** | No annotations in Haskell/OCaml |
| **Let-polymorphism** | Polymorphic let bindings |
| **Unification** | Type checking algorithm |
| **Principal types** | Most general type inferred |
| **Occurs check** | Prevents infinite types |

### Algorithm W in Practice

Most ML-family compilers use variants of Algorithm W:
- **OCaml**: Classic Algorithm W with extensions
- **Haskell**: Algorithm W + type classes + extensions
- **Rust**: Local type inference (not full HM)
- **F#**: Algorithm W on .NET

### Why HM Matters

1. **Productivity**: Write less, get same safety
2. **Refactoring**: Change signature → errors show where to update
3. **Documentation**: Inferred types are documentation
4. **Generics for free**: No manual type parameters

## References

### Essential Reading

1. **Damas, Luis and Milner, Robin** (1982). "Principal Type-Schemes for Functional Programs." *POPL*.
   Original paper on Algorithm W. Proves soundness, completeness, and principal types.
   [ACM DL](https://dl.acm.org/doi/10.1145/582153.582176) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=7453965783765422042)

2. **Hindley, J. Roger** (1969). "The Principal Type-Scheme of an Object in Combinatory Logic." *Trans. AMS*.
   Independent discovery of type inference.
   [AMS](https://www.ams.org/journals/tran/1969-146-00/S0002-9947-1969-0253905-6/) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=16871187286604568900)

3. **Milner, Robin** (1978). "A Theory of Type Polymorphism in Programming." *JCSS*.
   Foundational paper on ML type system.
   [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0022000078900144) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=4334544669712632498)

4. **Pierce, Benjamin C.** (2002). *Types and Programming Languages*. MIT Press.
   Chapter 22: Type Reconstruction. Excellent presentation of Algorithm W.
   [MIT Press](https://www.cis.upenn.edu/~bcpierce/tapl/) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=2853553209915529600)

5. **Cardelli, Luca** (1987). "Basic Polymorphic Typechecking." *Science of Computer Programming*.
   Clear algorithmic presentation.
   [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0167642387900190) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=4664725779762600556)

### Advanced Topics

6. **Rémy, Didier** (1992). "Extension of ML Type System with a Sorted Equational Theory on Types." *INRIA*.
   Row polymorphism for records.
   [HAL](https://hal.inria.fr/inria-00077006) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=7410270044612679060)

7. **Jones, Mark P.** (1992). "A Theory of Qualified Types." *ESOP*.
   Type classes for Haskell.
   [SpringerLink](https://link.springer.com/chapter/10.1007/3-540-55253-7_17) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=8556090399082029493)

8. **Odersky, Martin and Läufer, Konstantin** (1996). "Putting Type Annotations to Work." *POPL*.
   Local type inference.
   [ACM DL](https://dl.acm.org/doi/10.1145/237721.237729) |
   [Google Scholar](https://scholar.google.com/scholar?cluster=11364467204887709896)

### Implementation

9. **Heeren, Bastiaan; Hage, Jurriaan; Swierstra, Doaitse** (2002). "Generalizing Hindley-Milner Type Inference Algorithms." *Utrecht University Technical Report*.
   Modern treatment of type inference algorithms.
   [Google Scholar](https://scholar.google.com/scholar?cluster=5731157297390955667)

10. **Online Resources**:
    - [Write You a Haskell](http://dev.stephendiehl.com/fun/006_hindley_milner.html) by Stephen Diehl
    - Algorithm W Step by Step by Martin Grabmüller

## Exercises

1. Add type-level let bindings (type synonyms)
2. Implement Algorithm J (bidirectional type inference)
3. Add extensible records with row polymorphism
4. Implement ML-style modules and signatures
5. Add simple type classes
6. Compare inference times: Algorithm W vs Algorithm M
7. Implement constraint-based type inference
8. Add GADTs with type inference

## Next Chapter

In [Chapter 5](../chapter-05-system-f), we move to **System F** (polymorphic lambda calculus) with explicit type abstraction and application, enabling first-class polymorphism.
