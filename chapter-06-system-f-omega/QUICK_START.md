# Chapter 6: System F-omega - Quick Start

## TL;DR

**Higher-kinded types!** Types that take types as arguments. Now you can abstract over type constructors like `List`, `Maybe`. This is Haskell's full power and Scala's higher-kinded types.

**Time**: 2-3 weeks | **Prerequisites**: Chapter 5

## What You'll Build

- Kind system (*, * → *, (* → *) → *)
- Type-level lambda abstraction
- Higher-kinded type operators
- Functor and Monad at the type level

**Outcome**: Program at the type level!

## 5-Minute Setup

```bash
cd chapter-06-system-f-omega
stack build
stack exec system-f-omega-repl
```

### Quick Win (3 minutes)

```
λω> :tlet List = /\A::*. forall B::*. (A->B->B)->B->B
  List :: * → *

λω> :kind List
  List :: * → *

λω> :kind List Nat
  List Nat :: *

λω> :tlet Functor = /\F::*->*. forall A::*. forall B::*.
                      (A -> B) -> F A -> F B
  Functor :: (* → *) → *

Type constructors as arguments!
```

**Achievement**: Type-level abstraction! 🎯

## Key Concepts

```
* = proper types (Nat, Bool)
* → * = type constructors (List, Maybe)
(* → *) → * = higher-kinded (Functor, Monad)
```

## Next Steps

1. **Tutorial**: `TUTORIAL.md` (90 min) - kinds explained
2. **Practice**: `REPL_GUIDE.md` - Functor/Monad
3. **Exercises**: `exercises/EXERCISES.md`
4. **Test**: `QUIZ.md`

## Quick Reference

```
# Kinds
:kind <type>           # Show kind
* = value types
* → * = type constructors
(* → *) → * = higher-kinded

# Type-Level Lambda
:tlet List = /\A::*. ...    # Type operator
List Nat                     # Type application

# Higher-Kinded
:tlet Functor = /\F::*->*. ...
```

## Success Criteria

- [ ] Understand kinds
- [ ] Define type operators
- [ ] Implement Functor
- [ ] Complete exercises 1-4

**Time**: 14-20 hours | **Help**: `REPL_GUIDE.md`, `COMMON_MISTAKES.md`
