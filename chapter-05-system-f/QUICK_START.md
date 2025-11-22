# Chapter 5: System F - Quick Start

## TL;DR

**Explicit polymorphism** - YOU control type abstraction! Write `/\A. \x:A. x` and apply with `[Nat]`. More verbose than HM but MORE EXPRESSIVE. This is Java generics, C# generics, and Scala's foundation.

**Time**: 2-3 weeks | **Prerequisites**: Chapter 2 or 4

## What You'll Build

- Type abstraction (`Λα. t`) and application (`t [T]`)
- Church encodings at the type level
- Understanding of parametricity
- Foundation of modern generics

**Outcome**: Encode ANY data type using only functions!

## 5-Minute Setup

```bash
cd chapter-05-system-f
stack build
stack exec system-f-repl
```

### Quick Win (3 minutes)

```
λ> /\A. \x:A. x
  : ∀A. A → A
  Λα. λx:α. x

λ> (/\A. \x:A. x) [Nat] zero
  : Nat
  0

λ> :tlet Bool = forall A. A -> A -> A
λ> :let true = /\A. \t:A. \f:A. t
  true : ∀A. A → A → A

You just implemented Church booleans!
```

**Achievement**: Type-level programming! 🎭

## Key Differences from Chapter 4

| Hindley-Milner (Ch4) | System F (Ch5) |
|---------------------|----------------|
| `\x. x` | `/\A. \x:A. x` |
| Automatic | Explicit |
| `id 42` | `id [Nat] 42` |
| Decidable inference | Undecidable |

## Next Steps

1. **Tutorial**: `TUTORIAL.md` (75 min) - Church encodings
2. **Practice**: `REPL_GUIDE.md` - build data types
3. **Exercises**: `exercises/EXERCISES.md` 1-6
4. **Test**: `QUIZ.md`

## Quick Reference

```
# Type Abstraction/Application
/\A. term              # Type abstraction (Λα)
term [Type]            # Type application

# Church Encodings
:tlet Bool = forall A. A -> A -> A
:let true = /\A. \t:A. \f:A. t
:let false = /\A. \t:A. \f:A. f

# Type Bindings
:tlet Name = Type      # Save type
:tbindings             # Show types
```

## Success Criteria

- [ ] Understand `/\A` vs `\x`
- [ ] Implement Church booleans
- [ ] Grasp parametricity
- [ ] Complete exercises 1-5

**Time**: 12-18 hours | **Help**: `REPL_GUIDE.md`, `COMMON_MISTAKES.md`
