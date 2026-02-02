# Chapter 8: Full Dependent Types - Quick Start

## TL;DR

**Consistent foundation for mathematics!** Universe hierarchy fixes Type:Type paradox. Propositional equality (Eq type) lets you PROVE things. J eliminator enables all equality reasoning. This IS Agda/Coq/Lean!

**Time**: 4-6 weeks | **Prerequisites**: Chapter 7

## What You'll Build

- Universe hierarchy (Type : Type1 : Type2 : ...)
- Propositional equality (Eq A x y)
- J eliminator for equality proofs
- Inductive families (Vec, Fin)
- Full Curry-Howard correspondence

**Outcome**: Verified programming! Programs that are provably correct!

## 5-Minute Setup

```bash
cd chapter-08d-dependent-types-patterns
stack build
stack exec dependent-types-patterns-repl
```

### Quick Win (3 minutes)

```
λU> Type
  : Type1
  (No more Type:Type paradox!)

λU> refl zero
  : Eq Nat 0 0
  (Proof that zero equals zero!)

λU> :let sym = \(A:Type). \(x:A). \(y:A). \(eq:Eq A x y).
                 J A (\(a:A). \(b:A). \(e:Eq A a b). Eq A b a)
                     (\(z:A). refl z) x y eq
  sym : Π(A:Type). Π(x:A). Π(y:A). Eq A x y → Eq A y x
  
Proved symmetry using J!

λU> Vec Nat 3
  : Type
  (Vectors with length in the type!)
```

**Achievement**: Theorem proving! 🏆

## Key Additions from Chapter 7

```
Universe Hierarchy: Type : Type1 : Type2 : ...
Equality: Eq A x y (propositional equality)
J Eliminator: Prove properties of equality
Inductive Families: Vec, Fin
```

## Next Steps

1. **Must Read**: `FAQ.md` - universes & equality explained
2. **Tutorial**: `TUTORIAL.md` (3+ hours) - J eliminator mastery
3. **Practice**: `REPL_GUIDE.md` - prove theorems!
4. **Exercises**: `exercises/EXERCISES.md`
5. **Test**: `QUIZ.md`

## Quick Reference

```
# Universes
Type : Type1 : Type2 : ...

# Equality
Eq A x y               # Equality type
refl x                 # Reflexivity
J ...                  # Equality induction

# Eliminators
natElim                # Nat recursion
boolElim               # Bool case analysis
vecElim                # Vec recursion

# Inductive Families
Vec A n                # Length-indexed vectors
Fin n                  # Numbers < n
```

## Success Criteria

- [ ] Understand universes
- [ ] Use refl and J
- [ ] Prove symmetry/transitivity
- [ ] Work with Vec and Fin
- [ ] Complete exercises 1-3

**Time**: 20-30 hours | **Help**: `FAQ.md`, `REPL_GUIDE.md`, `COMMON_MISTAKES.md`

Congratulations! You've reached the pinnacle of type systems! 🎓✨
