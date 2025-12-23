# Chapter 19: Bidirectional Type Checking - Quick Start

## TL;DR (30 seconds)

Bidirectional type checking splits type checking into two modes: **inference** (⇒) computes types, **checking** (⇐) verifies them. This gives minimal annotations with predictable behavior. Introduction forms check, elimination forms infer. In 5 minutes, you'll type-check your first bidirectional term!

**Who**: Students who understand simply-typed lambda calculus
**Time**: 1-2 weeks (or 3-4 intensive days)
**Payoff**: Foundation for modern type systems (dependent types, higher-rank polymorphism)

## What You'll Build

- Bidirectional type checker with two mutually recursive functions
- Understanding of when annotations are needed
- Ability to classify constructs by mode
- Foundation for advanced type systems

**Tangible Outcome**: A type checker that accepts `λx. x` when given an expected type but rejects it without one!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-19-bidirectional-typing
stack build
stack exec bidir-repl
```

You should see:
```
Welcome to the Bidirectional Type Checker REPL!
bidir>
```

### Step 2: Your First Inference (1 minute)

```
bidir> true
true ⇒ Bool
Value: true
```

Variables and constants can be inferred!

### Step 3: The Key Insight (1 minute)

Try to infer a lambda:
```
bidir> \x. x
Cannot infer type for this term
Hint: Use annotation or :check command
```

Now check it:
```
bidir> :check \x. x : Bool -> Bool
✓ λx. x ⇐ Bool → Bool
Value: <λx. ...>
```

### Step 4: Make It Inferrable (1 minute)

Add an annotation:
```
bidir> (\x. x : Bool -> Bool)
(λx. x : Bool → Bool) ⇒ Bool → Bool
Value: <λx. ...>
```

Or annotate the parameter:
```
bidir> \(x : Bool). x
λ(x : Bool). x ⇒ Bool → Bool
Value: <λx. ...>
```

## Your First Success - Bidirectional Typing (10 minutes)

Follow this mini-tutorial to cement your understanding:

### 1. Understand the Two Modes

**Inference (⇒)**: Compute the type
```
bidir> true
true ⇒ Bool
```

**Checking (⇐)**: Verify against expected type
```
bidir> :check true : Bool
✓ true ⇐ Bool
```

### 2. Introduction vs Elimination

**Eliminations infer** (they use values):
```
bidir> \(f : Bool -> Bool). \(x : Bool). f x
λ(f : Bool → Bool). λ(x : Bool). f x ⇒ (Bool → Bool) → Bool → Bool
```

**Introductions check** (they create values):
```
bidir> :check \x. x : Bool -> Bool
✓ λx. x ⇐ Bool → Bool
```

### 3. Type Propagation

Checking mode propagates types inward:
```
bidir> :check (\x. (x, x)) : Bool -> (Bool × Bool)
✓ λx. (x, x) ⇐ Bool → (Bool × Bool)
```

The expected type tells us:
- `x : Bool` (from `Bool → ...`)
- Both components need `Bool` (from `... × Bool`)

### 4. The Annotation Trick

When inference fails, add an annotation:
```
bidir> \f. \x. f x
Cannot infer type

bidir> (\f. \x. f x : (Bool -> Bool) -> Bool -> Bool)
(λf. λx. f x : (Bool → Bool) → Bool → Bool) ⇒ (Bool → Bool) → Bool → Bool
```

**Achievement Unlocked**: You understand the two modes! 🎉

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - step-by-step walkthrough
2. Follow `LESSON_PLAN.md` - structured 10-14 hour course
3. Use `CHEAT_SHEET.md` as reference
4. Try the first 5 exercises in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal rules (30 minutes)
2. Work through exercises 1-10 (2-3 hours)
3. Study `src/TypeCheck.hs` implementation
4. Take `QUIZ.md` to verify understanding

### For Explorers
1. Open `REPL_GUIDE.md` and try all examples
2. Experiment with `:infer` vs `:check` commands
3. Study derivation trees with `:derivation`
4. Try to break the type checker!

## When to Skip This Chapter

**Skip if**:
- You already understand bidirectional typing
- You've read Pierce & Turner's "Local Type Inference"
- You just want unification-based inference (see Chapter 4)

**Don't skip if**:
- You're learning about modern type systems
- You want to understand dependent types later
- You're interested in type system design
- You care about predictable type inference

## Quick Reference

```bash
# Build
cd chapter-19-bidirectional-typing && stack build

# Run REPL
stack exec bidir-repl

# Essential REPL Commands
:help               # Show help
:infer term         # Infer type (⇒)
:check term : type  # Check type (⇐)
:derivation term    # Show derivation tree
:quit               # Exit

# Lambda Syntax
\x. x                      # Unannotated lambda (checks only)
\(x : Bool). x             # Annotated lambda (infers)
(\x. x : Bool -> Bool)     # Term annotation (infers)
\x y. x                    # Multi-arg lambda

# Your First Definitions
:let id = \(x : Bool). x
:let const = \(x : Bool). \(y : Nat). x
:let apply = \(f : Bool -> Bool). \(x : Bool). f x
```

## Success Criteria

You're ready for advanced type systems when you can:
- [ ] Classify constructs as inference or checking
- [ ] Explain why unannotated lambdas can't be inferred
- [ ] Write derivation trees
- [ ] Know when annotations are needed
- [ ] Implement basic bidirectional type checker

**Minimum**: Understand the two modes and when to use each
**Ideal**: Complete all exercises and implement extensions

## Time Investment

- **Minimum**: 3 hours (basics only)
- **Recommended**: 10-14 hours (solid understanding)
- **Complete**: 20 hours (all exercises + implementation)

## Common Pitfalls

### Pitfall 1: Wrong Mode for Construct
```
bidir> \x. x
Cannot infer  ❌

bidir> :check \x. x : Bool -> Bool
✓  ✓
```

**Remember**: Unannotated lambdas check, don't infer.

### Pitfall 2: Forgetting Subsumption
If you can infer it, you can check it:
```
bidir> :check true : Bool
✓ true ⇐ Bool  (via subsumption)
```

### Pitfall 3: Wrong Application Direction
The function is inferred, the argument is checked:
```
Γ ⊢ f ⇒ A → B    Γ ⊢ x ⇐ A
────────────────────────────
Γ ⊢ f x ⇒ B
```

Not the other way around!

## The Two Key Rules

### Rule 1: Introduction → Check
Creating values needs context:
- `λx. e` - need expected function type
- `(e₁, e₂)` - need expected product type
- `inl e` - need expected sum type

### Rule 2: Elimination → Infer
Using values provides context:
- `e₁ e₂` - infer function type
- `fst e` - infer product type
- `case e of ...` - infer sum type

## Quick Examples

### Example 1: Why Annotation Helps
```
Without annotation (fails):
  \x. x
  No rule applies in inference mode!

With parameter annotation (works):
  \(x : Bool). x
  Uses annotated lambda rule ⇒ Bool → Bool

With term annotation (works):
  (\x. x : Bool -> Bool)
  Uses annotation rule: check λx.x against type
```

### Example 2: Type Propagation
```
bidir> :check (\x. \y. (x, y)) : Bool -> Nat -> (Bool × Nat)

Outer lambda: x : Bool
Inner lambda: y : Nat
Pair: first needs Bool, second needs Nat

All type info flows from the outside annotation!
```

### Example 3: Application
```
bidir> (\(f : Bool -> Bool). \(x : Bool). f x) (\(y : Bool). y) true

1. Infer outer lambda: (Bool→Bool) → Bool → Bool
2. Infer inner lambda: Bool → Bool
3. Check it against Bool→Bool ✓
4. Return: Bool → Bool
5. Check true against Bool ✓
6. Return: Bool
```

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md`
- **Need examples?** See `REPL_GUIDE.md`
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Reference**: `CHEAT_SHEET.md` for quick lookup
- **Practice**: `PRACTICE_PROBLEMS.md` for extra exercises

## What Makes Bidirectional Special?

1. **Minimal annotations**: Only where truly needed
2. **Predictable**: You know what needs annotations
3. **Local**: No global unification
4. **Extensible**: Easy to add new features
5. **Foundation**: Scales to dependent types

## Real-World Applications

Bidirectional typing is used in:
- **Agda**: Dependently typed language
- **Idris**: Practical dependent types
- **TypeScript**: Local type inference
- **Typed Racket**: Gradual typing
- **PureScript**: Row polymorphism

## Mini-Project: Extend the Checker

Try these extensions (30 minutes each):

1. **Add Unit Type**
   ```
   Unit type and unit value
   ```

2. **Add Let Bindings**
   ```
   let x = e1 in e2
   ```

3. **Add If-Then-Else**
   ```
   if c then t else e
   ```

4. **Better Errors**
   ```
   Track mode in error messages
   ```

## The Big Picture

```
Inference (⇒)          Checking (⇐)
     ↓                      ↓
Compute type           Verify type
     ↓                      ↓
Variables              Lambdas
Application            Pairs
Annotated λ            Injections
Annotations            Type abstraction
Projections
Type application
     ↓                      ↓
   ←──── Subsumption ────→
   (if inferred = expected)
```

Good luck! You're learning a technique used in cutting-edge type systems! 🚀
