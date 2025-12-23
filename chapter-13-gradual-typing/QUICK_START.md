# Chapter 13: Gradual Typing - Quick Start

## TL;DR (30 seconds)

Gradual typing bridges static and dynamic typing using the dynamic type `?`. It's **consistency** (not equality!), runtime casts, and blame tracking. This chapter teaches you how to mix typed and untyped code safely. In 5 minutes, you'll understand the core idea!

**Who**: Anyone who knows basic type systems (Chapter 2)
**Time**: 2-3 weeks (or 1 intensive week)
**Payoff**: Understand TypeScript, Python type hints, and gradual migration strategies

## What You'll Learn

- The dynamic type `?` and consistency relation
- How casts bridge static/dynamic boundaries
- Blame tracking for runtime errors
- Gradual migration from dynamic to static
- Connection to real languages (TypeScript, Python)

**Tangible Outcome**: Design a gradual migration strategy for a real codebase!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-13-gradual-typing
stack build
stack exec gradual-repl
```

You should see:
```
Welcome to the Gradual Typing REPL!
gradual>
```

### Step 2: Your First Dynamic Type (1 minute)

```
gradual> :type λx : ?. x
? -> ?
```

Congrats! You just wrote a function that accepts ANY type!

### Step 3: Mixing Types (1 minute)

```
gradual> :type λf : ? -> Nat. λx : ?. f x
(? -> Nat) -> ? -> Nat
```

This takes a dynamic function (that returns `Nat`) and a dynamic argument!

### Step 4: See the Casts (1 minute)

```
gradual> :casts (λx : ?. x + 1) 42
(λx : ?. <? => Nat>^body x + 1) <Nat => ?>^arg 42
```

The REPL shows you the runtime casts inserted automatically!

## Your First Success - Understanding Consistency (10 minutes)

### 1. Consistency vs Equality

Type equality is too strict:
```
gradual> :check λf : Nat -> Bool. λx : Nat. f x
Nat -> Bool → Nat -> Bool  ✓ (types equal)

gradual> :check λf : ? -> Bool. λx : Nat. f x
ERROR: Nat ≠ ?  ✗ (with equality)
```

But with consistency:
```
gradual> :check λf : ? -> Bool. λx : Nat. f x
(? -> Bool) -> Nat -> Bool  ✓ (Nat ~ ?)
```

### 2. Dynamic is Consistent with Everything

```
gradual> :consistent Nat ?
true

gradual> :consistent ? (Nat -> Bool)
true

gradual> :consistent (? -> ?) (Nat -> Bool)
true
```

### 3. But NOT Transitive!

```
gradual> :consistent Nat ?
true

gradual> :consistent ? Bool
true

gradual> :consistent Nat Bool
false  -- NOT transitive!
```

**Achievement Unlocked**: You understand the core of gradual typing! 🎉

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - step-by-step examples
2. Follow `LESSON_PLAN.md` - structured 12-16 hour course
3. Use `REPL_GUIDE.md` for interactive exploration
4. Try exercises 1-5 in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (45 minutes)
2. Work through exercises 1-10 (3-4 hours)
3. Check solutions in `exercises/Solutions.hs`
4. Take `QUIZ.md` to verify understanding

### For Practitioners
1. Read "Gradual Migration" section in `TUTORIAL.md`
2. Study TypeScript examples in `README.md`
3. Design migration for your own codebase
4. Use `:casts` command to understand runtime behavior

## When to Skip This Chapter

**Skip if**:
- You only care about pure static typing
- You never work with dynamic languages
- You've studied gradual typing formally before

**Don't skip if**:
- You use TypeScript, Python type hints, or similar
- You want to migrate dynamic code to typed
- You're curious about type system theory
- You work with FFI or untyped libraries

## Core Concepts (10 minutes)

### The Dynamic Type `?`

Think of `?` as "unknown type, check at runtime":

```
x : ?           -- x could be anything
f : ? -> Nat    -- f takes unknown, returns Nat
g : Nat -> ?    -- g takes Nat, returns unknown
```

### Consistency Relation `~`

Replaces type equality in gradual systems:

```
? ~ T           ✓ for any T
T ~ ?           ✓ for any T
T ~ T           ✓ (reflexive)
T₁ -> T₂ ~ S₁ -> S₂   ✓ if T₁ ~ S₁ and T₂ ~ S₂
```

**Critical**: NOT transitive!

### Casts `<T₁ => T₂>^l`

Bridge between types with runtime checks:

```
<Nat => ?>       -- Inject Nat into dynamic
<? => Bool>      -- Project dynamic to Bool (may fail!)
```

The label `l` tracks blame when casts fail.

### Blame

When a cast fails:
```
<Bool => Nat>^myLabel true  →  blame^myLabel
```

The label identifies the responsible code location.

## Quick Reference

```bash
# Build
cd chapter-13-gradual-typing && stack build

# Run REPL
stack exec gradual-repl

# Essential REPL Commands
:help               # Show all commands
:type <term>        # Show type
:casts <term>       # Show elaborated term with casts
:consistent T S     # Check if T ~ S
:reduce <term>      # Step-by-step reduction
:quit               # Exit

# Syntax
λx : ?. x           # Dynamic identity
λf : ? -> Nat. f 0  # Apply dynamic function
<Nat => ?> 42       # Explicit cast
```

## Example Session

```
gradual> :type λx : ?. x
? -> ?

gradual> :type (λx : ?. x + 1) 42
Nat

gradual> :casts (λx : ?. x + 1) 42
(λx : ?. <? => Nat>^body x + 1) <Nat => ?>^arg 42

gradual> :reduce (λx : ?. x) (<Nat => ?> 42)
Step 1: (<? => ?> (<Nat => ?> 42))
Step 2: <Nat => ?> 42
Result: 42 (after cast optimization)

gradual> :consistent (Nat -> Bool) (? -> ?)
true

gradual> :consistent Nat Bool
false
```

## Success Criteria

You're ready for the next chapter when you can:
- [ ] Explain the dynamic type `?`
- [ ] Check type consistency
- [ ] Understand cast insertion
- [ ] Trace blame in examples
- [ ] Design gradual migration strategies

**Minimum**: Understand consistency and casts
**Ideal**: Complete exercises 1-10 and understand blame tracking

## Time Investment

- **Minimum**: 4 hours (core concepts only)
- **Recommended**: 12-16 hours (solid understanding)
- **Complete**: 24 hours (all exercises + advanced topics)

## Common Pitfalls

### Pitfall 1: Assuming Transitivity
```
Nat ~ ?  and  ? ~ Bool
does NOT imply  Nat ~ Bool
```

### Pitfall 2: Confusing Cast Direction
```
<Bool => ?>     -- Safe injection
<? => Bool>     -- May fail (projection)
```

### Pitfall 3: Ignoring Blame
```
(λx : ?. x + 1) "hello"  -- Where's the error?
-- Inside lambda when casting ? => Nat
```

### Pitfall 4: TypeScript ≠ Gradual Typing
TypeScript's `any` is **unsound**:
```typescript
let x: any = "hello";
let y: number = x;  // No runtime check!
y + 1;  // "hello1" - Bug!
```

Proper gradual typing would insert real casts.

## Real-World Examples

### TypeScript
```typescript
// any is like ?
function process(data: any): number {
  return data.length;  // Hope data has length!
}
```

### Python
```python
from typing import Any

def compute(x: Any) -> int:
    return x + 1  # Hope x is a number!
```

### Typed Racket
```racket
;; Explicit typed/untyped boundaries
(require/typed "untyped-lib.rkt"
  [process (-> Any String)])
```

## Help & Resources

- **Stuck on consistency?** Check `CHEAT_SHEET.md` for rules
- **Need examples?** See `TUTORIAL.md` for walkthroughs
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Practice**: `PRACTICE_PROBLEMS.md` has 25+ problems

## Connection to Other Chapters

- **Chapter 9 (Subtyping)**: Gradual subtyping combines both
- **Chapter 6 (Polymorphism)**: Gradual polymorphism extends parametric types
- **Chapter 14 (Row Types)**: Gradual rows for extensible records

## What Makes This Chapter Special

Gradual typing is **practical theory**:
- TypeScript uses it (imperfectly)
- Python's type hints use it
- Critical for migrating legacy code
- Bridges academic and industry needs

Unlike pure type systems, gradual typing acknowledges the **messy reality** of software development.

## Your First Exercise

Try this now:

```
gradual> :type λx : ?. λy : Nat. x + y
```

What type do you get? Why?

<details>
<summary>Answer</summary>

Type: `? -> Nat -> Nat`

Explanation:
- `x : ?` is cast to `Nat` when used in `x + y`
- `y : Nat` is already typed
- Result is `Nat`
- Full term: `(λx : ?. λy : Nat. (<? => Nat> x) + y)`
</details>

## Next Chapter Preview

Chapter 14 (Row Types) explores **structural polymorphism** - work with records having "at least" certain fields. It's orthogonal to gradual typing but can be combined!

Good luck! You're learning a **practical and powerful** type system feature! 🚀
