# Chapter 22: Constraint-Based Type Inference

**Constraint-based type inference** separates type inference into two distinct phases:
1. **Constraint Generation**: Walk the AST and generate equality constraints between types
2. **Constraint Solving**: Solve the constraints using unification to find a most general unifier (MGU)

This approach is more **modular** and **extensible** than Algorithm W, making it easier to add new type system features.

## Overview

| **Aspect** | **Algorithm W** | **Constraint-Based** |
|------------|----------------|---------------------|
| **Structure** | Single pass, interleaved | Two-phase (generate + solve) |
| **Extensibility** | Hard to extend | Easy to add new constraints |
| **Debugging** | Implicit constraints | Explicit constraint sets |
| **Error Messages** | Point-specific | Can show all conflicts |
| **Connection to SMT** | None | Natural extension |

## Key Concepts

### 1. Constraints

A **constraint** is a requirement that must be satisfied by the types:

```haskell
data Constraint
  = Equal Type Type           -- τ₁ ≡ τ₂  (equality)
  | Subtype Type Type         -- τ₁ <: τ₂ (subtyping, optional)
  | HasField Type Label Type  -- τ has field ℓ:τ' (records, optional)
```

For basic Hindley-Milner, we only need **equality constraints**.

### 2. Constraint Generation

Generate constraints by walking the AST:

```
Γ ⊢ e ⇝ τ | C

Where:
  Γ = type environment
  e = expression
  τ = inferred type (may contain fresh variables)
  C = set of constraints
```

**Generation Rules:**

```
[Var]
x:σ ∈ Γ    τ = instantiate(σ)
────────────────────────────────
Γ ⊢ x ⇝ τ | ∅


[Lam]
α fresh    Γ, x:α ⊢ e ⇝ τ | C
────────────────────────────────
Γ ⊢ λx.e ⇝ α → τ | C


[App]
Γ ⊢ e₁ ⇝ τ₁ | C₁    Γ ⊢ e₂ ⇝ τ₂ | C₂    α fresh
────────────────────────────────────────────────────
Γ ⊢ e₁ e₂ ⇝ α | C₁ ∪ C₂ ∪ {τ₁ ≡ τ₂ → α}


[If]
Γ ⊢ e₁ ⇝ τ₁ | C₁    Γ ⊢ e₂ ⇝ τ₂ | C₂    Γ ⊢ e₃ ⇝ τ₃ | C₃
────────────────────────────────────────────────────────────
Γ ⊢ if e₁ then e₂ else e₃ ⇝ τ₂ | C₁ ∪ C₂ ∪ C₃ ∪ {τ₁ ≡ Bool, τ₂ ≡ τ₃}


[Let]
Γ ⊢ e₁ ⇝ τ₁ | C₁    solve(C₁) = σ    Γ, x:generalize(σ(τ₁)) ⊢ e₂ ⇝ τ₂ | C₂
───────────────────────────────────────────────────────────────────────────────
Γ ⊢ let x = e₁ in e₂ ⇝ τ₂ | C₁ ∪ C₂
```

### 3. Constraint Solving (Unification)

Given a constraint set `C`, find a substitution `σ` such that `σ(C)` holds.

**Robinson's Unification Algorithm:**

```
unify(τ₁, τ₂) =
  case (τ₁, τ₂) of
    (τ, τ)           → {}                    -- identical types
    (α, τ)           → {α ↦ τ}  if α ∉ ftv(τ)  -- bind variable
    (τ, α)           → {α ↦ τ}  if α ∉ ftv(τ)
    (τ₁→τ₂, τ₃→τ₄)   → σ₂ ∘ σ₁  where σ₁ = unify(τ₁,τ₃)
                                        σ₂ = unify(σ₁(τ₂), σ₁(τ₄))
    (τ₁×τ₂, τ₃×τ₄)   → similar to function case
    _                → fail     -- unification failure
```

**Occurs Check:** Prevent infinite types by checking `α ∉ ftv(τ)` before binding.

### 4. Most General Unifier (MGU)

The **most general unifier** is the *least specific* substitution that satisfies all constraints:

```haskell
-- Example:
-- Constraints: {t0 ≡ Bool, t1 ≡ t0 → Nat}
-- MGU: {t0 ↦ Bool, t1 ↦ Bool → Nat}
```

Any other valid substitution is an *instance* of the MGU.

## Examples

### Example 1: Identity Function

**Term:** `λx. x`

**Constraint Generation:**
```
α fresh (for x)
x:α ⊢ x ⇝ α | ∅         (lookup, no constraints!)
─────────────────────────
⊢ λx. x ⇝ α → α | ∅
```

**Constraints:** `∅` (empty)

**Solving:** No constraints to solve

**Type:** `t0 → t0` (polymorphic!)

### Example 2: Successor Function

**Term:** `λx. succ x`

**Constraint Generation:**
```
α fresh (for x)
x:α ⊢ x ⇝ α | ∅
x:α ⊢ succ x ⇝ Nat | {α ≡ Nat}    (succ requires Nat)
──────────────────────────────────
⊢ λx. succ x ⇝ α → Nat | {α ≡ Nat}
```

**Constraints:** `{α ≡ Nat}`

**Solving:**
```
σ = unify(α, Nat) = {α ↦ Nat}
```

**Type:** `Nat → Nat`

### Example 3: Application

**Term:** `(λf. λx. f x) (λy. succ y)`

**Constraint Generation:**
```
Generate for λf. λx. f x:
  α fresh (for f)
  β fresh (for x)
  γ fresh (for result)
  Constraints: {α ≡ β → γ}
  Type: α → β → γ

Generate for λy. succ y:
  δ fresh (for y)
  Constraints: {δ ≡ Nat}
  Type: δ → Nat

Application constraint:
  {α → β → γ ≡ (δ → Nat) → ε}  where ε fresh
```

**All Constraints:**
```
{
  α ≡ β → γ,           -- f must be a function
  δ ≡ Nat,             -- y must be Nat
  α ≡ δ → Nat,         -- match function type
  β ≡ Nat,             -- from unifying above
  γ ≡ Nat              -- from unifying above
}
```

**Solving:**
```
σ₁ = {δ ↦ Nat}
σ₂ = {α ↦ Nat → Nat}
σ₃ = {β ↦ Nat, γ ↦ Nat}
Final: {α ↦ Nat → Nat, β ↦ Nat, γ ↦ Nat, δ ↦ Nat}
```

**Type:** `Nat → Nat`

### Example 4: Let-Polymorphism

**Term:** `let id = λx. x in (id true, id 0)`

**Constraint Generation:**
```
Generate for λx. x:
  Type: α → α
  Constraints: ∅

Generalize: ∀α. α → α

Instantiate id at first use: β → β (fresh β)
Instantiate id at second use: γ → γ (fresh γ)

Constraints from uses:
  {β → β ≡ Bool → δ,    -- id true
   γ → γ ≡ Nat → ε}      -- id 0
```

**Solving:**
```
σ = {β ↦ Bool, δ ↦ Bool, γ ↦ Nat, ε ↦ Nat}
```

**Type:** `Bool × Nat`

**Note:** This works because `id` is generalized! Compare with:

**Term (fails):** `(λid. (id true, id 0)) (λx. x)`

Here `id` has a **monomorphic** type in the lambda, so it can't be used at both `Bool → Bool` and `Nat → Nat`.

## Why Constraint-Based Inference is Better

### 1. Modularity

Adding new type features is easier:

```haskell
-- Add subtyping constraints:
data Constraint
  = Equal Type Type
  | Subtype Type Type      -- NEW!

-- Constraint generation for subsumption:
Γ ⊢ e ⇝ τ | C    τ <: σ expected
────────────────────────────────────
Γ ⊢ e ⇝ σ | C ∪ {τ <: σ}
```

### 2. Better Error Messages

With Algorithm W, you get errors at specific points. With constraints, you can:
- Show **all** unsatisfiable constraints
- Explain **why** constraints arise
- Suggest **fixes** based on constraint structure

### 3. Debugging

Constraints make the type inference process **explicit**:

```
:constraints λx. succ x
Shows:
  t1 ≡ Nat
```

You can see exactly what requirements the type checker has!

### 4. Connection to SMT Solvers

Constraint-based inference naturally extends to **dependent types** and **refinement types**:

```haskell
-- Refinement type constraints:
data Constraint
  = Equal Type Type
  | Refinement Var Type Predicate    -- {x:τ | P(x)}

-- Example: non-negative integers
Γ ⊢ x ⇝ Int | {x ≥ 0}
```

Modern type systems (F\*, Liquid Haskell, Dafny) use SMT solvers to check these constraints.

## Common Errors

### 1. Occurs Check Failure

**Example:** `λx. x x`

**Constraints:**
```
α fresh (for x)
β fresh (for result)
x:α ⊢ x x ⇝ β | {α ≡ α → β}
```

**Error:** `α` occurs in `α → β`, creating an **infinite type**.

**Why it fails:** `α = α → β = (α → β) → β = ((α → β) → β) → β = ...`

### 2. Type Mismatch

**Example:** `if 0 then true else false`

**Constraints:**
```
{
  Nat ≡ Bool,    -- condition must be Bool
  Bool ≡ Bool    -- branches must match
}
```

**Error:** Cannot unify `Nat` and `Bool`

### 3. Non-Polymorphic Lambda

**Example:** `λf. (f true, f 0)`

**Constraints:**
```
α fresh (for f)
{
  α ≡ Bool → β,    -- from f true
  α ≡ Nat → γ      -- from f 0
}
```

**Error:** Cannot unify `Bool → β` with `Nat → γ` (requires `Bool ≡ Nat`)

## Implementation Details

### Constraint Generation Monad

```haskell
newtype ConstraintGen a = ConstraintGen
  (ExceptT ConstraintError (State Int) a)

-- Fresh type variable generation
fresh :: ConstraintGen Type
fresh = do
  n <- get
  put (n + 1)
  return $ TyVar ("t" ++ show n)
```

### Solving Algorithm

```haskell
solve :: ConstraintSet -> Either SolveError Subst
solve = solveConstraints emptySubst
  where
    solveConstraints s [] = return s
    solveConstraints s (Equal t1 t2 : cs) = do
      let t1' = applySubst s t1
      let t2' = applySubst s t2
      s' <- unify t1' t2'
      solveConstraints (s' `composeSubst` s) cs
```

## REPL Usage

The REPL provides special commands for inspecting constraints:

```haskell
-- Show generated constraints
λ> :constraints λx. succ x
Constraints:
  t1 ≡ Nat
Inferred type: t1 -> Nat

-- Show full solving process
λ> :solve λf. λx. f x
Generated constraints:
  t1 ≡ t2 -> t3
Solved with substitution:
  {t1 ↦ t2 -> t3}
Final type: (t2 -> t3) -> t2 -> t3

-- Demonstrate unification
λ> :unify (t0 -> t1) (Bool -> t2)
Most general unifier:
  {t0 ↦ Bool, t1 ↦ t2}
```

## Comparison with Algorithm W

**Algorithm W** (Chapter 4):
- ✅ Simple, direct
- ❌ Hard to extend
- ❌ Implicit constraints
- ❌ Limited error messages

**Constraint-Based** (This chapter):
- ✅ Modular, extensible
- ✅ Explicit constraints (better debugging)
- ✅ Better error messages
- ✅ Foundation for advanced features
- ❌ Slightly more complex implementation

## Extensions

Constraint-based inference makes it easy to add:

1. **Subtyping** (see Chapter 9)
   - Add `Subtype` constraints
   - Use constraint-based subsumption checking

2. **Type Classes** (Haskell)
   - Add `InstanceOf` constraints
   - Resolve during constraint solving

3. **Refinement Types**
   - Add `Refinement` constraints
   - Use SMT solver for satisfiability

4. **Effects** (Algebraic effects)
   - Add `Effect` constraints
   - Track effect polymorphism

5. **Regions** (Memory management)
   - Add `Region` constraints
   - Lifetime tracking

## Further Reading

### Papers

1. **"A Theory of Type Polymorphism in Programming"** - Milner (1978)
   - [Google Scholar](https://scholar.google.com/scholar?q=A+Theory+of+Type+Polymorphism+in+Programming)
   - Original formulation of type inference

2. **"Constraint-based type inference in FreezeML"** - Parreaux et al. (2020)
   - [Google Scholar](https://scholar.google.com/scholar?q=Constraint-based+type+inference+in+FreezeML)
   - Modern approach to ML-style inference

3. **"Practical type inference for arbitrary-rank types"** - Peyton Jones et al. (2007)
   - [Google Scholar](https://scholar.google.com/scholar?q=Practical+type+inference+for+arbitrary-rank+types)
   - OutsideIn algorithm (GHC Haskell)

4. **"Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"** - Dunfield & Krishnaswami (2013)
   - [Google Scholar](https://scholar.google.com/scholar?q=Complete+and+Easy+Bidirectional+Typechecking)
   - Bidirectional approach with constraints

### Books

- **Types and Programming Languages** (Pierce, 2002) - Chapter 22
- **Advanced Topics in Types and Programming Languages** (Pierce, 2004)
- **Programming Language Foundations in Agda** (Wadler et al., 2022)

### Tools

- **Liquid Haskell**: Refinement type checker using SMT
- **F\***: Dependently-typed language with SMT-based verification
- **Dafny**: Verification-aware language with constraints

## Summary

Constraint-based type inference:
1. **Separates** constraint generation from solving
2. Makes type requirements **explicit**
3. Is **easier to extend** with new features
4. Provides **better error messages**
5. Forms the **foundation** for advanced type systems

This approach is used in modern type checkers for Haskell (GHC), OCaml, Scala, and many research languages.
