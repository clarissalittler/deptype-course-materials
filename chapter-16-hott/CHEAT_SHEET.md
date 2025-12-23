# Chapter 16: Homotopy Type Theory - Cheat Sheet

## The Big Idea

| Type Theory | Homotopy/Topology |
|-------------|-------------------|
| Type A | Space/∞-groupoid A |
| Term a : A | Point a in space A |
| Id A a b | Paths from a to b |
| Path between paths | Homotopy (2-path) |

## Syntax

```
T ::=                          (types)
    Id A a b                   identity type (path type)
    A → B                      function type
    ...                        other types

t ::=                          (terms)
    refl [A] a                 reflexivity (trivial path)
    J C base a b p             path induction (J eliminator)
    sym p                      symmetry (path inverse)
    trans p q                  transitivity (path composition)
    ap f p                     action on paths
    transport P p x            transport along path
    absurd [T] t               ex falso (from empty type)
```

## Core Concepts

### Identity Type

```
Id A a b    -- Type of paths from a to b in A
a =_A b     -- Alternative notation
```

**Intuition**: The type of proofs that a equals b, or paths connecting a to b.

### Reflexivity

```
refl : (a : A) → Id A a a
```

**Intuition**: The constant/trivial path at a point—staying in place.

## Path Induction (J Eliminator)

```
J : (C : (x y : A) → Id A x y → Type) →  -- motive
    ((x : A) → C x x refl) →              -- base case
    (a b : A) → (p : Id A a b) →          -- inputs
    C a b p                                -- result
```

**Key Principle**: To prove something for all paths, it suffices to prove it for refl.

**Computation Rule**:
```
J C base a a refl ≡ base a
```

J only computes (definitional equality) on refl paths!

## Path Operations

### Symmetry (Path Inverse)

```
sym : Id A a b → Id A b a

-- Computation
sym refl ≡ refl
```

**Intuition**: Reverse direction of a path.

### Transitivity (Path Composition)

```
trans : Id A a b → Id A b c → Id A a c

-- Computation
trans refl q ≡ q
trans p refl ≡ p    (propositionally, not definitionally!)
```

**Intuition**: Walk path p, then walk path q.

### Action on Paths (Functoriality)

```
ap : (f : A → B) → Id A a b → Id B (f a) (f b)

-- Computation
ap f refl ≡ refl
```

**Intuition**: Functions preserve paths (are "continuous").

### Transport (Path Lifting)

```
transport : (P : A → Type) → Id A a b → P a → P b

-- Computation
transport P refl x ≡ x
```

**Intuition**: Paths in the base space lift to paths in the fiber.

## Path Algebra (Groupoid Laws)

### Groupoid Structure

Types form ∞-groupoids with paths as morphisms:

| Law | Statement | Type |
|-----|-----------|------|
| Left identity | `trans refl p = p` | `Id (Id A a b) (trans refl p) p` |
| Right identity | `trans p refl = p` | `Id (Id A a b) (trans p refl) p` |
| Inverse left | `trans p (sym p) = refl` | `Id (Id A a a) (trans p (sym p)) refl` |
| Inverse right | `trans (sym p) p = refl` | `Id (Id A a a) (trans (sym p) p) refl` |
| Associativity | `trans (trans p q) r = trans p (trans q r)` | `Id (Id A a d) ...` |

**Key**: These equalities are themselves paths (2-paths)!

### Path Composition Rules

```
  a --p--> b --q--> c
  =
  a ----trans p q----> c
```

Middle points must match:
```
trans : Id A a b → Id A b c → Id A a c
                   ^^^   ^^^
                   must match!
```

## Derivations from J

### Deriving sym

```
C = λx y p. Id A y x
base = λx. refl
sym p = J C base a b p
```

### Deriving transport

```
C = λx y p. P x → P y
base = λx. λz. z    -- identity
transport P p = J C base a b p
```

### Deriving ap

```
C = λx y p. Id B (f x) (f y)
base = λx. refl
ap f p = J C base a b p
```

## Higher Path Structure

### Level Hierarchy

- **0-paths**: Points (terms)
- **1-paths**: Paths between points (`Id A a b`)
- **2-paths**: Paths between paths (`Id (Id A a b) p q`)
- **3-paths**: Paths between 2-paths
- **∞-paths**: Continues infinitely

### h-Levels

| Level | Name | Meaning |
|-------|------|---------|
| -2 | Contractible | Unique point up to path |
| -1 | Proposition | At most one element |
| 0 | Set | All paths are equal (UIP) |
| 1 | Groupoid | Paths form sets |
| 2 | 2-groupoid | 2-paths form sets |

## Typing Rules

### Reflexivity

```
   Γ ⊢ a : A
────────────────────── (T-Refl)
 Γ ⊢ refl a : Id A a a
```

### J Eliminator

```
Γ ⊢ C : (x y : A) → Id A x y → Type
Γ ⊢ base : (x : A) → C x x refl
Γ ⊢ a, b : A
Γ ⊢ p : Id A a b
──────────────────────────────────── (T-J)
      Γ ⊢ J C base a b p : C a b p
```

### Symmetry

```
  Γ ⊢ p : Id A a b
─────────────────────── (T-Sym)
 Γ ⊢ sym p : Id A b a
```

### Transitivity

```
Γ ⊢ p : Id A a b    Γ ⊢ q : Id A b c
──────────────────────────────────── (T-Trans)
      Γ ⊢ trans p q : Id A a c
```

### ap

```
Γ ⊢ f : A → B    Γ ⊢ p : Id A a b
──────────────────────────────────── (T-Ap)
 Γ ⊢ ap f p : Id B (f a) (f b)
```

### Transport

```
Γ ⊢ P : A → Type    Γ ⊢ p : Id A a b    Γ ⊢ x : P a
───────────────────────────────────────────────────── (T-Transport)
           Γ ⊢ transport P p x : P b
```

## Evaluation Rules

```
-- Symmetry on refl
sym (refl a) → refl a

-- Transitivity on refl
trans (refl a) (refl a) → refl a
trans (refl a) p → p    (when p is a value)

-- ap on refl
ap f (refl a) → refl (f a)

-- transport on refl
transport P (refl a) x → x

-- J on refl
J C base a a (refl a) → base a
```

## Common Patterns

### Pattern 1: Proving Path Properties

To prove `P : (x y : A) → Id A x y → Type`:
1. Define motive C
2. Prove base case for refl
3. Apply J

### Pattern 2: Path Composition

```
a --p--> b --q--> c
```
becomes `trans p q : Id A a c`

### Pattern 3: Path Reversal

```
a --p--> b
```
becomes `b --sym p--> a`

### Pattern 4: Function Application

```
a --p--> b    f : A → B
```
implies `f a --ap f p--> f b`

## Univalence (Conceptual)

```
(A ≃ B) ≃ (A = B)
```

**Meaning**: Equivalent types are equal types.

**NOT**: All types are equal!

**Requires**: An equivalence `A ≃ B` to get a path `Id Type A B`.

## Higher Inductive Types (Conceptual)

Types with both point and path constructors:

### The Circle

```
data S¹ where
  base : S¹
  loop : Id S¹ base base    -- Non-trivial path!
```

### The Sphere

```
data S² where
  base : S²
  surf : Id (Id S² base base) refl refl    -- 2-dimensional!
```

## Practical Examples

### Basic Paths

```
refl [Nat] 0 : Id Nat 0 0

sym (refl [Nat] 0) : Id Nat 0 0    -- evaluates to refl

trans (refl [Nat] 0) (refl [Nat] 0) : Id Nat 0 0
-- evaluates to refl
```

### Function Application

```
f = λx:Nat. succ x
ap f (refl [Nat] 0) : Id Nat (succ 0) (succ 0)
-- evaluates to refl [Nat] (succ 0)
```

### Transport

```
transport [λx:Bool. Nat] (refl [Bool] true) (succ 0)
-- evaluates to succ 0
```

## Remember

### Do
- Think of types as spaces, terms as points, equalities as paths
- Use J for path induction
- Remember computation rule: J only reduces on refl
- Understand path algebra is itself built from paths

### Avoid
- Thinking Id A a b is just a boolean
- Assuming unique identity proofs (UIP)—HoTT rejects this!
- Expecting J to compute on all paths
- Confusing definitional (≡) and propositional (=) equality

## Definitional vs Propositional

| Aspect | Definitional (≡) | Propositional (=) |
|--------|------------------|-------------------|
| When | Computation rules | Proven theorems |
| Example | `sym refl ≡ refl` | `trans p (sym p) = refl` |
| Substitution | Automatic | Need transport/J |
| Checking | Syntactic | Requires proof |

## Quick Reference Card

### Creating Paths
```
refl a                 -- Trivial path at a
```

### Using Paths
```
sym p                  -- Reverse
trans p q              -- Compose
ap f p                 -- Apply function
transport P p x        -- Lift along path
```

### Proving About Paths
```
J C base a b p         -- Path induction
```

### Type Patterns
```
Id A a b               -- Path from a to b
Id (Id A a b) p q      -- Path between paths (2-path)
```

## Debugging Tips

1. **Type error on sym**: Check endpoints match after reversal
2. **Type error on trans**: Check middle points match
3. **J doesn't compute**: Are you using refl? J only computes on refl
4. **Confused about higher paths**: Draw a diagram
5. **Need UIP**: You're not in HoTT! HoTT doesn't assume UIP

## Further Reading

- **HoTT Book**: The definitive reference
- **Egbert Rijke (2022)**: Intro to Homotopy Type Theory
- **Escardó (2019)**: Intro with Agda
- **Cubical Type Theory**: Computational univalence

## Connection to Other Concepts

- **Equality**: Generalized to paths
- **Substitution**: Generalized to transport
- **Induction**: Generalized to path induction
- **Fixed points**: μ types ↔ HITs (higher inductive types)

## Next Steps

- **Cubical type theory**: Computational paths and univalence
- **Proof assistants**: Agda --cubical, Arend, redtt
- **Synthetic homotopy theory**: Prove topological theorems in type theory
