# Chapter 4: Hindley-Milner Type Inference - Quick Start

## TL;DR

**NO TYPE ANNOTATIONS NEEDED!** The type system figures out types automatically. This is the magic behind ML, OCaml, Haskell, and F#. Write `\x. x` instead of `\x:T. x` and get full type safety!

**Time**: 2-3 weeks | **Prerequisites**: Chapter 2

## What You'll Build

- Automatic type inference (Algorithm W)
- Polymorphic types (∀a. a → a)
- Let-polymorphism
- Understanding of principal types

**Outcome**: Types without the annotation burden!

## 5-Minute Setup

```bash
cd chapter-04-hindley-milner
stack build
stack exec hindley-milner-repl
```

### Quick Win (3 minutes)

```
λ> \x. x
  : ∀a. a → a
  λx. x

No type annotation! The system inferred it!

λ> \f g x. f (g x)
  : ∀a b c. (b → c) → (a → b) → a → c
  λf. λg. λx. f (g x)

Inferred the composition type automatically!

λ> let id = \x. x in (id 1, id true)
  : (Int, Bool)
  (1, true)

One function, multiple types!
```

**Achievement**: Polymorphism without annotations! 🔮

## Key Insight: Let vs Lambda

```
λ> let id = \x. x in id id        ✓ Works! (let is polymorphic)
λ> (\id. id id) (\x. x)            ✗ Fails! (lambda is monomorphic)
```

This is THE crucial difference in Hindley-Milner!

## Next Steps

1. **Must Read**: `FAQ.md` - answers the big questions
2. **Tutorial**: `TUTORIAL.md` (90 min) - Algorithm W explained
3. **Practice**: `REPL_GUIDE.md` exercises on polymorphism
4. **Exercises**: `exercises/EXERCISES.md` 1-6
5. **Test**: `QUIZ.md`

## When to Skip

**Skip if**: Familiar with ML-style type inference
**Don't skip if**: First time with automatic inference or polymorphism

## Quick Reference

```
# No Annotations!
\x. x               # Not \x:T. x
\f x. f x           # Types inferred

# Polymorphic Types
∀a. a → a           # Works for ANY type
∀a b. a → b → a     # Two type variables

# Let-Polymorphism
let f = \x. x in ...    # f is polymorphic
(\f. ...) (\x. x)       # f is monomorphic

# REPL Commands
:type <term>        # See inferred type
:infer <term>       # Show inference steps
```

## Success Criteria

Ready for Chapter 5 when you:
- [ ] Write terms without annotations
- [ ] Understand polymorphic types
- [ ] Grasp let vs lambda difference
- [ ] Can debug unification errors
- [ ] Complete exercises 1-7

**Time**: 12-16 hours | **Help**: `FAQ.md` (READ THIS!), `COMMON_MISTAKES.md`

Welcome to the magic of type inference! ✨
