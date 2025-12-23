# Quick Start: Constraint-Based Type Inference

## Build and Run

```bash
cd chapter-22-constraint-inference

# Build
stack build

# Run REPL
stack run constraint-inference-repl

# Run tests
stack test
```

## First Steps

### 1. Basic Inference

```haskell
λ> \x. x
  : t0 -> t0

λ> \x. succ x
  : Nat -> Nat
```

### 2. View Constraints

```haskell
λ> :constraints \x. succ x
Generated constraints:
  t1 ≡ Nat
Inferred type (before solving): t1 -> Nat
```

### 3. Full Solving Process

```haskell
λ> :solve \f. \g. \x. f (g x)
Generated constraints:
  t1 ≡ t2 -> t3
Solved with substitution:
  {t1 ↦ t2 -> t3}
Final type: (t2 -> t3) -> (t4 -> t2) -> t4 -> t3
```

### 4. Test Unification

```haskell
λ> :unify (t0 -> t1) (Bool -> t2)
Most general unifier:
  {t0 ↦ Bool, t1 ↦ t2}

λ> :unify t0 (t0 -> Bool)
Unification failed: OccursCheck "t0" (TyArr (TyVar "t0") TyBool)
```

## Key Commands

| Command | Description |
|---------|-------------|
| `:type term` | Show inferred type |
| `:constraints term` | Show generated constraints |
| `:solve term` | Show full solving process |
| `:unify ty1 ty2` | Demonstrate unification |
| `:help` | Show all commands |

## Example Session

```haskell
λ> :constraints let id = \x. x in (id 0, id true)
Generated constraints:
  t3 ≡ Nat
  t5 ≡ Bool
Inferred type: Nat * Bool

λ> :solve \f. (f 0, f true)
Generated constraints:
  t1 ≡ Nat -> t2
  t1 ≡ Bool -> t3
Unification failed: Cannot unify (Nat -> t2) and (Bool -> t3)
```

## Next Steps

- Read [README.md](README.md) for theory
- Try [exercises/EXERCISES.md](exercises/EXERCISES.md)
- Compare with Chapter 4 (Algorithm W)
