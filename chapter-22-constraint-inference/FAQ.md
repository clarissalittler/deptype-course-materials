# FAQ: Constraint-Based Type Inference

## General Questions

### Q: What's the difference between constraint-based inference and Algorithm W?

**A:** Both achieve the same result (Hindley-Milner type inference), but differ in structure:

- **Algorithm W**: Single-pass algorithm that interleaves constraint generation and solving
- **Constraint-Based**: Two-phase approach that separates generation from solving

**Advantages of constraint-based:**
1. More modular - easier to add new features
2. Better error messages - can show all constraints
3. Easier to debug - explicit constraint sets
4. Foundation for advanced features (subtyping, effects, refinements)

### Q: Why do we need the occurs check?

**A:** The occurs check prevents **infinite types**. Consider `λx. x x`:

Without occurs check:
```
α ≡ α → β
α = α → β = (α → β) → β = ((α → β) → β) → β = ...
```

This creates an infinite type! The occurs check catches this: if we're trying to bind `α ↦ τ` and `α` appears in `τ`, we fail.

### Q: What's let-polymorphism?

**A:** Let-polymorphism allows let-bound variables to be used at **different types**:

```haskell
let id = λx. x in (id 0, id true)  -- OK! id used at Nat→Nat and Bool→Bool
```

But lambda-bound variables are **monomorphic**:

```haskell
(λid. (id 0, id true)) (λx. x)     -- Error! id must have ONE type
```

**Why?** Let-bindings **generalize** (introduce ∀), lambdas don't.

### Q: When should I use constraint-based inference vs Algorithm W?

**A:**

Use **Algorithm W** when:
- You want a simple, direct implementation
- You're implementing basic Hindley-Milner
- You don't need extensibility

Use **Constraint-Based** when:
- You plan to add features (subtyping, effects, etc.)
- You need good error messages
- You're building a research language
- You want to connect to SMT solvers

## Constraint Generation

### Q: Why do we need fresh type variables?

**A:** Fresh variables prevent **accidental sharing** of constraints:

```haskell
-- BAD: reusing α
λx. λy. x    -- both x and y get type α? NO!

-- GOOD: fresh variables
λx. λy. x    -- x:α, y:β, type: α → β → α
```

Each binding site needs its own variable!

### Q: How do constraints from different parts combine?

**A:** Constraints are **accumulated** (union) as you walk the AST:

```haskell
if e₁ then e₂ else e₃
  Constraints from e₁: C₁
  Constraints from e₂: C₂
  Constraints from e₃: C₃
  New constraints: {τ₁ ≡ Bool, τ₂ ≡ τ₃}
  Total: C₁ ∪ C₂ ∪ C₃ ∪ {τ₁ ≡ Bool, τ₂ ≡ τ₃}
```

### Q: What happens when I generate constraints for `let`?

**A:** Two approaches:

**Simple approach** (used in basic implementation):
- Generate constraints for the bound expression
- Generalize the type immediately
- Generate constraints for the body

**Proper approach** (more complex):
- Generate constraints for the bound expression
- **Solve those constraints first**
- Generalize the resulting type
- Generate constraints for the body

The proper approach gives more accurate polymorphism!

## Constraint Solving

### Q: What is a most general unifier (MGU)?

**A:** The **least specific** substitution that makes types equal:

```haskell
Example: unify (t0 → t1) with (Bool → t2)

Solutions:
  {t0 ↦ Bool, t1 ↦ Nat, t2 ↦ Nat}  -- valid but too specific
  {t0 ↦ Bool, t1 ↦ t2}              -- MGU! Most general
```

Any valid substitution is an **instance** of the MGU.

### Q: Why do we compose substitutions?

**A:** When solving multiple constraints, we must **apply previous substitutions**:

```haskell
Constraints: {t0 ≡ Bool, t1 ≡ t0 → Nat}

Step 1: Solve t0 ≡ Bool
  σ₁ = {t0 ↦ Bool}

Step 2: Solve t1 ≡ t0 → Nat
  Apply σ₁: t1 ≡ Bool → Nat  (substitute t0!)
  σ₂ = {t1 ↦ Bool → Nat}

Compose: σ = σ₂ ∘ σ₁ = {t0 ↦ Bool, t1 ↦ Bool → Nat}
```

### Q: What's the order of solving constraints?

**A:** For **equality constraints**, order doesn't matter (they commute):

```haskell
{t0 ≡ Bool, t1 ≡ Nat} = {t1 ≡ Nat, t0 ≡ Bool}
```

But for **subtyping** or **other** constraints, order may matter!

### Q: Can constraint solving fail?

**A:** Yes, in two ways:

1. **Occurs check**: `t0 ≡ t0 → Bool`
2. **Type clash**: `Bool ≡ Nat`

Both indicate the term doesn't type check.

## Common Errors

### Q: Why does `λx. x x` fail?

**A:** Self-application requires `x : α` and `x : α → β` simultaneously:

```
Constraint: α ≡ α → β
Occurs check: α appears in α → β!
Error: Infinite type
```

### Q: Why does `λf. (f 0, f true)` fail?

**A:** `f` must be used at **one** type (it's lambda-bound, not let-bound):

```
From f 0: f : Nat → β
From f true: f : Bool → γ
Unify: Nat → β ≡ Bool → γ
  ⇒ Nat ≡ Bool  (FAIL!)
```

### Q: Why does `if 0 then true else false` fail?

**A:** `if` requires a `Bool` condition:

```
Constraint: Nat ≡ Bool
Error: Type mismatch
```

## Advanced Topics

### Q: Can I add subtyping to constraint-based inference?

**A:** Yes! Add a new constraint type:

```haskell
data Constraint
  = Equal Type Type
  | Subtype Type Type    -- τ₁ <: τ₂
```

Then modify the solver to handle subtyping constraints.

### Q: How do I handle recursive functions?

**A:** Use `let` with a fixed-point:

```haskell
let fact = λn. if iszero n then 1 else n * fact (pred n)
```

The `let` allows `fact` to refer to itself (through the environment).

### Q: Can constraint-based inference handle dependent types?

**A:** Not directly, but it's a foundation:

1. **Bidirectional typing**: Mix inference and checking
2. **Refinement types**: Add logical constraints to SMT solver
3. **Dependent types**: Require more sophisticated constraint languages

### Q: What's the connection to SMT solvers?

**A:** Constraint-based inference naturally extends to **logical constraints**:

```haskell
-- Refinement types
{x : Int | x ≥ 0}

-- Encoded as constraints
Constraint: Refines x Int (x ≥ 0)

-- Solved using SMT (Z3, CVC4, etc.)
```

Languages like F* and Liquid Haskell use this approach!

## Debugging

### Q: How do I debug type errors?

**A:** Use the `:constraints` and `:solve` commands:

```haskell
λ> :constraints your-term
-- Shows what constraints are generated

λ> :solve your-term
-- Shows the solving process

-- If it fails, you see exactly which constraint is unsolvable
```

### Q: What does "cannot unify X with Y" mean?

**A:** Two types are required to be equal but can't be:

```
Cannot unify Bool with Nat
  ⇒ The type checker needs Bool and Nat to be the same type
  ⇒ They're not, so it fails
```

Look at the constraint set to see **why** this constraint arose.

### Q: How can I see the type of a subexpression?

**A:** Use `:type` with the subexpression:

```haskell
-- Full term
λ> :type λf. λx. f (f x)

-- Subexpression
λ> :type λf. λx. f x
```

## Performance

### Q: Is constraint-based inference slower than Algorithm W?

**A:** Potentially, but not significantly:

- **Overhead**: Building constraint sets, composing substitutions
- **Benefit**: Can optimize solving (constraint simplification, early failure)

In practice, both are fast enough for most programs.

### Q: Can I optimize constraint solving?

**A:** Yes! Several techniques:

1. **Constraint simplification**: Remove trivial constraints
2. **Early failure**: Detect unification failures early
3. **Lazy solving**: Only solve constraints when needed
4. **Constraint graph**: Use graph structure for efficiency

## Tools and Languages

### Q: What languages use constraint-based inference?

**A:**

- **OCaml**: Modern implementation uses constraints
- **Haskell (GHC)**: OutsideIn algorithm (constraint-based)
- **Scala**: DOT calculus with constraints
- **F\***: Refinement types with SMT constraints
- **Liquid Haskell**: Refinement types over Haskell

### Q: Where can I learn more?

**A:** See the README's "Further Reading" section, and explore:

1. "Constraint-based type inference in FreezeML" (Parreaux et al., 2020)
2. "OutsideIn(X)" (Vytiniotis et al., 2011) - GHC's algorithm
3. "Complete and Easy Bidirectional Typechecking" (Dunfield & Krishnaswami, 2013)
