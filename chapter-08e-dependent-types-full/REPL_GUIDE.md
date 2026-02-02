# Chapter 8: Full Dependent Types - REPL User Guide

## Overview

The Full Dependent Types REPL represents the pinnacle of type systems: a **consistent foundation for mathematics and verified programming**. It extends Chapter 7 with universe hierarchy (eliminating the Type-in-Type paradox), propositional equality, and inductive families. This is the system used by modern proof assistants!

**Key Additions**: Universe hierarchy, Eq type, J eliminator, inductive families, eliminators

**Achievement**: Complete Curry-Howard correspondence - programs ARE proofs!

## Getting Started

### Building and Running

```bash
# Build the REPL
cd chapter-08e-dependent-types-full
stack build

# Run the REPL
stack exec dependent-types-full-repl
```

### Your First Universe-Polymorphic Term

```
λU> \(A:Type). \(x:A). x
  : Π(A:Type). A → A
  λ(A:Type). λ(x:A). x

λU> refl zero
  : Eq Nat 0 0
  refl 0

λU> Type
  : Type1
  Type

λU> Type1
  : Type2
  Type1

λU> :help
  [Shows available commands]
```

**Note**: Universe hierarchy prevents paradoxes!

## Features

### 1. Universe Hierarchy - Consistency!

Infinite hierarchy of universes:

```
λU> Type
  : Type1
  (Type 0 lives in Type 1)

λU> Type1
  : Type2
  (Type 1 lives in Type 2)

λU> Type2
  : Type3
  (and so on, infinitely)

λU> :type Nat
  Nat : Type
  (Nat lives in Type 0)

λU> :type Type -> Type
  (Type → Type) : Type1
  (type-level functions live in Type 1)
```

**Key**: No more Type : Type paradox!

### 2. Propositional Equality - Eq Type

The equality type represents proofs of equality:

```
λU> Eq Nat zero zero
  : Type
  (the type of proofs that zero equals zero)

λU> refl zero
  : Eq Nat 0 0
  (reflexivity proof - the trivial proof)

λU> Eq Nat (succ zero) 1
  : Type
  (type of proofs that 1 = 1)

λU> refl (succ zero)
  : Eq Nat 1 1
```

**Syntax**: `Eq A x y` is the type of proofs that x = y in type A

### 3. Reflexivity - refl

The constructor for equality:

```
λU> refl zero
  : Eq Nat 0 0
  (every value is equal to itself)

λU> refl true
  : Eq Bool true true

λU> refl (\(x:Nat). x)
  : Eq (Nat → Nat) (λ(x:Nat). x) (λ(x:Nat). x)

λU> \(A:Type). \(x:A). refl x
  : Π(A:Type). Π(x:A). Eq A x x
  (reflexivity for all types)
```

### 4. J Eliminator - Equality Induction

The elimination principle for equality (most powerful tool!):

```
λU> :type J
  J : Π(A:Type).
      Π(C:Π(x:A). Π(y:A). Eq A x y → Type).
      Π(c:Π(x:A). C x x (refl x)).
      Π(x:A). Π(y:A). Π(p:Eq A x y).
      C x y p

  (To prove property C for all equalities,
   prove it for refl!)
```

**Intuition**: All proofs of equality are essentially `refl`!

### 5. Symmetry via J

Prove x = y implies y = x:

```
λU> :let sym = \(A:Type). \(x:A). \(y:A). \(eq:Eq A x y).
                 J A
                   (\(x:A). \(y:A). \(e:Eq A x y). Eq A y x)
                   (\(z:A). refl z)
                   x y eq
  sym : Π(A:Type). Π(x:A). Π(y:A). Eq A x y → Eq A y x

λU> sym Nat zero zero (refl zero)
  : Eq Nat 0 0
  refl 0
```

### 6. Transitivity via J

Prove x = y and y = z implies x = z:

```
λU> :let trans = \(A:Type). \(x:A). \(y:A). \(z:A).
                   \(p:Eq A x y). \(q:Eq A y z).
                   J A
                     (\(x:A). \(y:A). \(e:Eq A x y).
                       Π(z:A). Eq A y z → Eq A x z)
                     (\(w:A). \(z:A). \(e:Eq A w z). e)
                     x y p z q
  trans : Π(A:Type). Π(x:A). Π(y:A). Π(z:A).
          Eq A x y → Eq A y z → Eq A x z
```

### 7. Natural Number Eliminator

Structural recursion via natElim:

```
λU> :type natElim
  natElim : Π(C:Nat → Type).
            C 0 →
            (Π(n:Nat). C n → C (succ n)) →
            Π(n:Nat). C n

  (To prove C for all n, prove for 0 and succ)

λU> :let add = \(m:Nat). \(n:Nat).
                 natElim
                   (\(_:Nat). Nat)  -- Motive
                   n                 -- Base case
                   (\(k:Nat). \(rec:Nat). succ rec)  -- Step
                   m
  add : Nat → Nat → Nat
```

### 8. Boolean Eliminator

```
λU> :type boolElim
  boolElim : Π(C:Bool → Type).
             C true →
             C false →
             Π(b:Bool). C b

λU> :let not = \(b:Bool).
                 boolElim
                   (\(_:Bool). Bool)  -- Motive
                   false               -- true case
                   true                -- false case
                   b
  not : Bool → Bool

λU> not true
  : Bool
  false

λU> not false
  : Bool
  true
```

### 9. Inductive Families - Vec

Vectors indexed by length:

```
λU> :type Vec
  Vec : Type → Nat → Type
  (vectors parameterized by element type and length)

λU> :type vnil
  vnil : Π(A:Type). Vec A 0
  (empty vector)

λU> :type vcons
  vcons : Π(A:Type). Π(n:Nat). A → Vec A n → Vec A (succ n)
  (cons that tracks length!)

λU> vcons Nat 0 zero (vnil Nat)
  : Vec Nat 1
  [0]

λU> vcons Nat 1 (succ zero) (vcons Nat 0 zero (vnil Nat))
  : Vec Nat 2
  [1, 0]
```

### 10. Finite Types - Fin

Natural numbers less than n:

```
λU> :type Fin
  Fin : Nat → Type
  (Fin n has exactly n inhabitants)

λU> :type fzero
  fzero : Π(n:Nat). Fin (succ n)
  (zero is less than any successor)

λU> :type fsucc
  fsucc : Π(n:Nat). Fin n → Fin (succ n)
  (if i < n then i+1 < n+1)

λU> fzero 0
  : Fin 1
  (the only element of Fin 1)

λU> fzero 2
  : Fin 3
  (0 < 3)

λU> fsucc 2 (fzero 1)
  : Fin 3
  (1 < 3)
```

### 11. Vector Indexing

Safe array access using Fin:

```
λU> :let vindex = \(A:Type). \(n:Nat). \(v:Vec A n). \(i:Fin n).
                    vecElim A
                      (\(m:Nat). \(v:Vec A m). Fin m → A)
                      (\(i:Fin 0). emptyElim A i)  -- Empty case impossible
                      (\(n:Nat). \(x:A). \(xs:Vec A n).
                        \(rec:Fin n → A). \(i:Fin (succ n)).
                        finElim n
                          (\(_:Fin (succ n)). A)
                          x                    -- fzero case
                          rec                  -- fsucc case
                          i)
                      n v i
  vindex : Π(A:Type). Π(n:Nat). Vec A n → Fin n → A
  (indexing that CANNOT go out of bounds!)
```

### 12. Empty Type - ⊥

Type with no inhabitants:

```
λU> :type Empty
  Empty : Type
  (the empty type)

λU> :type emptyElim
  emptyElim : Π(C:Type). Empty → C
  (from falsehood, anything follows - ex falso quodlibet)

λU> :let absurd = \(A:Type). \(x:Empty). emptyElim A x
  absurd : Π(A:Type). Empty → A
  (if you have Empty, you can prove anything)
```

### 13. Step-by-Step with Eliminators

```
λU> :step
Step mode enabled

λU> natElim (\(_:Nat). Nat) zero (\(n:Nat). \(rec:Nat). succ rec) 2
  : Nat
  natElim ... 2
    [Press Enter]
→ (\(n:Nat). \(rec:Nat). succ rec) 1 (natElim ... 1)
    [Press Enter]
→ succ (natElim ... 1)
    [Press Enter]
→ succ ((\(n:Nat). \(rec:Nat). succ rec) 0 (natElim ... 0))
    [Press Enter]
→ succ (succ (natElim ... 0))
    [Press Enter]
→ succ (succ zero)
    [Press Enter]
→ 2
```

## Command Reference

### Essential Commands
- `:help` - Show help
- `:quit` - Exit
- `:type <term>` - Show type
- `:let <name> = <term>` - Bind term
- `:normalize <term>` - Normalize

### Universe Commands
- `:universe <term>` - Show universe level
- `:universes` - Show universe hierarchy

### Equality Commands
- `:equal <term1> <term2>` - Check definitional equality
- `:prove <prop>` - Help prove proposition (if available)

### Evaluation Commands
- `:step` - Step-by-step
- `:trace` - Show trace
- `:normalize` - Full normalization

### Environment Commands
- `:bindings` - Show bindings
- `:reset` - Clear all

## Guided Exploration

### Exercise 1: Universe Hierarchy (15 minutes)

Explore universes:

```
λU> :type Type
λU> :type Type1
λU> :type Type2

λU> :type Nat
λU> :type Bool
λU> :type Type -> Type

λU> :universe Nat
λU> :universe (Type -> Type)
λU> :universe Type1
```

**Question**: Why do we need infinitely many universes?

### Exercise 2: Reflexivity (10 minutes)

Basic equality proofs:

```
λU> refl zero
λU> refl true
λU> refl (\(x:Nat). x)

λU> :let reflexivity = \(A:Type). \(x:A). refl x
λU> :type reflexivity
λU> reflexivity Nat zero
λU> reflexivity Bool true
```

**Challenge**: What's the type of `refl refl`?

### Exercise 3: Symmetry (20 minutes)

Implement symmetry using J:

```
λU> :let sym = \(A:Type). \(x:A). \(y:A). \(eq:Eq A x y).
                 J A
                   (\(a:A). \(b:A). \(e:Eq A a b). Eq A b a)
                   (\(z:A). refl z)
                   x y eq
λU> :type sym

λU> sym Nat zero zero (refl zero)
λU> :let p = refl zero
λU> sym Nat zero zero p
```

**Challenge**: Prove symmetry is its own inverse: sym (sym p) = p.

### Exercise 4: Transitivity (25 minutes)

Chain equalities:

```
λU> :let trans = \(A:Type). \(x:A). \(y:A). \(z:A).
                   \(p:Eq A x y). \(q:Eq A y z).
                   J A
                     (\(a:A). \(b:A). \(e:Eq A a b).
                       Π(c:A). Eq A b c → Eq A a c)
                     (\(w:A). \(c:A). \(e:Eq A w c). e)
                     x y p z q

λU> trans Nat 0 0 0 (refl 0) (refl 0)
```

**Challenge**: Prove transitivity is associative.

### Exercise 5: Congruence (20 minutes)

If x = y then f x = f y:

```
λU> :let cong = \(A:Type). \(B:Type). \(f:A->B).
                  \(x:A). \(y:A). \(p:Eq A x y).
                  J A
                    (\(a:A). \(b:A). \(e:Eq A a b). Eq B (f a) (f b))
                    (\(z:A). refl (f z))
                    x y p
  cong : Π(A:Type). Π(B:Type). Π(f:A→B).
         Π(x:A). Π(y:A). Eq A x y → Eq B (f x) (f y)

λU> cong Nat Nat succ 0 0 (refl 0)
  : Eq Nat 1 1
```

**Challenge**: Implement `cong2` for binary functions.

### Exercise 6: Natural Number Induction (30 minutes)

Structural recursion:

```
λU> :let add = \(m:Nat). \(n:Nat).
                 natElim
                   (\(_:Nat). Nat)
                   n
                   (\(k:Nat). \(rec:Nat). succ rec)
                   m

λU> add 2 3

λU> :let mult = \(m:Nat). \(n:Nat).
                  natElim
                    (\(_:Nat). Nat)
                    0
                    (\(k:Nat). \(rec:Nat). add n rec)
                    m

λU> mult 2 3
```

**Challenge**: Prove `add m 0 = m` using J and natElim.

### Exercise 7: Vector Operations (35 minutes)

Safe list operations:

```
λU> :let vappend = \(A:Type). \(m:Nat). \(n:Nat).
                     \(xs:Vec A m). \(ys:Vec A n).
                     vecElim A
                       (\(k:Nat). \(v:Vec A k). Vec A (add k n))
                       ys
                       (\(k:Nat). \(x:A). \(xs:Vec A k).
                         \(rec:Vec A (add k n)).
                         vcons A (add k n) x rec)
                       m xs
  vappend : Π(A:Type). Π(m:Nat). Π(n:Nat).
            Vec A m → Vec A n → Vec A (add m n)

λU> :let v1 = vcons Nat 0 zero (vnil Nat)
λU> :let v2 = vcons Nat 1 (succ zero) v1
λU> vappend Nat 1 1 v1 v1
```

**Challenge**: Implement `vreverse`.

### Exercise 8: Decidable Equality (30 minutes)

Prove equality is decidable for Nat:

```
λU> :tlet Dec = \(A:Type). A + (A -> Empty)
  (Either a proof or a refutation)

λU> :let natEqDec = \(m:Nat). \(n:Nat). Dec (Eq Nat m n)
  (to be implemented using natElim)
```

**Challenge**: Implement decidable equality for Nat.

## Tips and Tricks

### Tip 1: Universes Prevent Paradoxes
```
λU> Type : Type1       ✓ Consistent
λU> Type : Type        ✗ (Chapter 7's inconsistency)
```

### Tip 2: J is All You Need for Equality
```
All equality proofs derived from J:
- Symmetry
- Transitivity
- Congruence
- Substitution
```

### Tip 3: Eliminators for Structural Recursion
```
natElim  -- For recursion on Nat
boolElim -- For case analysis on Bool
vecElim  -- For recursion on Vec
finElim  -- For recursion on Fin
emptyElim -- For ex falso
```

### Tip 4: Types Track Precise Properties
```
Vec A n              -- Exactly n elements
Fin n                -- Exactly n inhabitants
Eq A x y             -- Proof of equality
Empty                -- No inhabitants (false)
```

### Tip 5: Curry-Howard in Full Force
```
Type               = Proposition
Term : Type        = Proof of proposition
Eq A x y           = Equality proposition
refl x             = Reflexivity proof
J                  = Induction principle
```

## Troubleshooting

### Problem: "Universe inconsistency"
**Cause**: Trying to put Type in itself
**Solution**: Use Type1, Type2, etc.

### Problem: "Cannot eliminate into Type"
**Cause**: Trying to use large elimination inappropriately
**Solution**: Check your motive carefully

### Problem: "Dependent pattern match required"
**Cause**: Simple pattern match insufficient
**Solution**: Use `match t return P with ...` (or an eliminator)

### Problem: "Equality proof doesn't normalize"
**Cause**: Complex proof term
**Solution**: Use :normalize to simplify

## Syntax Reference

### Universes
```
Type              -- Type 0
Type1             -- Type 1
Type2             -- Type 2
...
```

### Equality
```
Eq A x y          -- Equality type
refl x            -- Reflexivity proof
J ...             -- J eliminator (equality induction)
```

### Eliminators
```
natElim ...       -- Natural number recursion
boolElim ...      -- Boolean case analysis
vecElim ...       -- Vector recursion
finElim ...       -- Finite type recursion
emptyElim ...     -- Ex falso quodlibet
```

### Inductive Families
```
Vec A n           -- Length-indexed vectors
Fin n             -- Numbers less than n
Empty             -- Empty type (⊥)
```

## Comparison with Previous Chapters

| Feature | Chapter 7 | Chapter 8 |
|---------|-----------|-----------|
| Consistency | No (Type:Type) | Yes! (universe hierarchy) |
| Equality | Definitional only | Propositional (Eq type) |
| Induction | Limited | Full (J, eliminators) |
| Inductive families | Basic | Complete (Vec, Fin) |
| Proof power | Limited | Complete |

## Connection to Real Languages

Full dependent types as in:
- **Agda**: Very similar system
- **Coq**: Calculus of Inductive Constructions
- **Lean 4**: Similar with optimizations
- **Idris 2**: With quantitative types

## Key Theoretical Properties

1. **Consistency**: No paradoxes (universe hierarchy)
2. **Strong Normalization**: All terms terminate
3. **Canonicity**: Closed terms of Nat normalize to numerals
4. **Decidable Type Checking**: Algorithm always terminates

## Next Steps

After mastering this REPL:
1. Complete exercises in `exercises/EXERCISES.md`
2. Work through `TUTORIAL.md`
3. Take `QUIZ.md`
4. Review `COMMON_MISTAKES.md`
5. Explore real proof assistants (Agda, Coq, Lean)!
6. Build verified programs!

## Quick Reference Card

```
# Building
stack build && stack exec dependent-types-full-repl

# Universe Hierarchy
Type : Type1 : Type2 : ...

# Equality
refl x : Eq A x x
J ... : equality induction
sym, trans, cong : derived from J

# Eliminators
natElim ... : Nat recursion
boolElim ... : Bool case analysis
vecElim ... : Vec recursion
emptyElim ... : ex falso

# Inductive Families
Vec A n : vectors of length n
Fin n : numbers < n
Empty : false/⊥

# Curry-Howard
Programs = Proofs
Types = Propositions
```

Congratulations! You've reached the pinnacle of type systems! 🎓🎉
