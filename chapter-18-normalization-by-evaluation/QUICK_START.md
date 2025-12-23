# Chapter 18: Normalization by Evaluation - Quick Start

## TL;DR (30 seconds)

Normalization by Evaluation (NbE) is a brilliant technique: use **Haskell's evaluation** for beta reduction, then **read back** the result into normal form. No need to define reduction rules! In 5 minutes, you'll normalize your first lambda term using NbE!

**Who**: Students with lambda calculus background (Chapter 1)
**Time**: 1-2 weeks
**Payoff**: Essential technique for type checkers and proof assistants

## What You'll Build

- Eval function (syntax → semantics)
- Quote function (semantics → normal form)
- Normalization = quote ∘ eval
- Type checking with definitional equality

**Tangible Outcome**: Normalize complex lambda terms instantly, check type equality for dependent types!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-18-normalization-by-evaluation
stack build
stack exec nbe-repl
```

You should see:
```
NbE REPL (Normalization by Evaluation)
nbe>
```

### Step 2: Your First Normalization (1 minute)

```
nbe> (\x. x) (\y. y)
Normal form: λy. y
```

Beta reduction happened automatically!

### Step 3: See the Phases (1 minute)

```
nbe> :trace (\x. x) 5

Eval phase:
  eval [] ((\x. x) 5)
  → vApp (VLam "x" (Closure [] (TVar 0))) (VInt 5)
  → applyClosure (Closure [] (TVar 0)) (VInt 5)
  → eval [VInt 5] (TVar 0)
  → VInt 5

Quote phase:
  quote 0 (VInt 5)
  → NfInt 5

Normal form: 5
```

### Step 4: Something Powerful (1 minute)

```
nbe> (\x. \y. x) true false
Normal form: true

nbe> ((\n. \f. \x. f (n f x)) (\f. \x. f x))
Normal form: λf. λx. f (f x)
```

That's Church numeral successor! `succ 1 = 2`.

## Your First Success - Understanding Eval and Quote (10 minutes)

### The Two Phases

```
Term ──eval──► Val ──quote──► Nf
```

### 1. Eval: Syntax to Semantics

```
nbe> :eval \x. x + 1
Value: VLam "x" (Closure [] (x + 1))
```

The lambda became a closure!

### 2. Quote: Semantics to Normal Form

```
nbe> :let val = VLam "x" (Closure [] (TVar 0))
nbe> :quote val
Normal form: λx. x
```

The closure became syntax again.

### 3. Full Normalization

```
nbe> :normalize ((\x. x + x) 3)

Eval: VInt 6
Quote: NfInt 6
Normal form: 6
```

**Achievement Unlocked**: You understand eval and quote!

## The Key Insight - Closures (5 minutes)

### What's a Closure?

A closure packages a lambda with its environment:

```
Closure env body = "function waiting for argument"
```

### See It in Action

```
nbe> :eval let y = 10 in \x. x + y
Value: VLam "x" (Closure {y→10} (x + y))
```

The closure captured `y = 10`!

### Apply the Closure

```
nbe> :normalize (let y = 10 in (\x. x + y) 5)

Eval:
  closure = VLam "x" (Closure {y→10} (x + y))
  applyClosure closure (VInt 5)
  = eval {y→10, x→5} (x + y)
  = 15

Normal form: 15
```

No substitution! Just environment lookup.

**Achievement Unlocked**: You understand closures!

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (90 minutes) - step-by-step walkthrough
2. Follow `LESSON_PLAN.md` - structured learning path
3. Use `REPL_GUIDE.md` when experimenting
4. Try exercises 1-3 in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (30 minutes)
2. Work through exercises 1-7 (3-4 hours)
3. Implement your own NbE for STLC
4. Take `QUIZ.md` to verify understanding

### For Type Theory Students
1. Study how NbE enables type checking
2. Implement definitional equality check
3. Extend to Pi types and universes
4. Read Abel (2013) for advanced topics

## When to Skip This Chapter

**Skip if**:
- You already understand NbE
- You've implemented NbE for dependent types
- You're not interested in type checker implementation

**Don't skip if**:
- Planning to implement a type checker
- Interested in dependent types (Chapter 19+)
- Want to understand modern proof assistants
- Curious about normalization techniques

## Quick Reference

```bash
# Build
cd chapter-18-normalization-by-evaluation && stack build

# Run REPL
stack exec nbe-repl

# REPL Commands
:help               # Show help
:eval <term>        # Show value (eval phase)
:quote <value>      # Show normal form (quote phase)
:normalize <term>   # Full normalization
:trace <term>       # Show both phases
:equal <t1> <t2>    # Check definitional equality
:quit               # Exit

# Syntax
\x. x               # Lambda
(\x. x) 5           # Application
Type                # Universe
(x : A) -> B        # Pi type
```

## Interactive Examples

### Example 1: Beta Reduction

```
nbe> :trace ((\x. x + 1) 5)

Eval:
  vApp (VLam "x" (Closure [] (TVar 0 + 1))) (VInt 5)
  → applyClosure (Closure [] (TVar 0 + 1)) (VInt 5)
  → eval [VInt 5] (TVar 0 + 1)
  → 6

Quote:
  quote 0 (VInt 6) → NfInt 6

Result: 6
```

Beta reduction happened in eval!

### Example 2: Fresh Variables

```
nbe> :trace \f. \x. f x

Quote (starting at level 0):
  quote 0 (VLam "f" (Closure [] ...))
  → fresh variable f₀ at level 0
  → applyClosure closure f₀
  → VLam "x" (Closure [f₀] ...)
  → quote 1 (VLam "x" ...)
    → fresh variable x₁ at level 1
    → applyClosure closure x₁
    → VNe (NApp (NVar 0) (NVar 1))
    → quote 2, convert levels to indices
  → λf. λx. f x

Result: λf. λx. f x
```

Fresh variables let us "peek inside" closures!

### Example 3: Neutral Terms

```
nbe> :eval \x. x 5
Value: VLam "x" (Closure [] (x 5))

nbe> :quote (quoting with fresh variable for x)
Normal form: λx. x 5

Explanation: When we apply the closure to fresh x₀:
  eval [VNe (NVar 0)] (TVar 0 applied to 5)
  → vApp (VNe (NVar 0)) (VInt 5)
  → VNe (NApp (NVar 0) (VInt 5))  -- Stuck! Keep as neutral
```

### Example 4: Type Equality

```
nbe> :equal (\x. x) (\y. y)
true

nbe> :equal ((\x. x) (\y. y)) (\z. z)
true

nbe> :equal (\x. x + 1) (\y. y + 2)
false
```

Equality = normalize both and compare!

## Success Criteria

You're ready for Chapter 19 when you can:
- [ ] Explain the eval and quote phases
- [ ] Trace normalization of simple terms
- [ ] Understand closures and fresh variables
- [ ] Explain de Bruijn levels vs indices
- [ ] Complete exercises 1-5

**Minimum**: Understand eval/quote and closures
**Ideal**: Implement NbE for STLC yourself

## Time Investment

- **Minimum**: 6 hours (understand basics)
- **Recommended**: 12-16 hours (implement STLC version)
- **Complete**: 24 hours (all exercises + Pi types)

## Common First Questions

### Q: Why not just use reduction rules?

**A:** NbE is simpler (Haskell does the work), more efficient (sharing via closures), and scales better (works for dependent types, universes, etc.).

### Q: What's a closure?

**A:** A closure is `Closure env body` - it packages a term with the environment where it was defined. When applied, we evaluate the body in that environment extended with the argument.

### Q: Why fresh variables in quote?

**A:** To "open" closures! A closure is opaque, but we can observe its behavior by applying it to a neutral variable and seeing what comes out.

### Q: Levels vs indices?

**A:** Indices count inward (from variable to binder), levels count outward (from root). Levels make fresh variable generation easy: just increment!

## Visual Aid: NbE Flow

```
      normalize
         │
    ┌────┴────┐
    │         │
   eval     quote
    │         │
    ▼         ▼
 Closure   Fresh vars
    │         │
    └────┬────┘
         │
    Normal form
```

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md`
- **Need examples?** See `REPL_GUIDE.md`
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Quick lookup**: `CHEAT_SHEET.md`

## Pro Tips

1. **Trace everything**: Use `:trace` to see eval and quote
2. **Draw closures**: Sketch environment on paper
3. **Count levels carefully**: Increment when entering binders
4. **Test on simple terms first**: Master identity before Church numerals
5. **Use :equal to experiment**: See what's definitionally equal

## First Exercise

Try this before moving on:

```
nbe> :trace (\x. \y. x) true false
```

Questions:
- What closure is created for `\y. x`?
- What environment does it capture?
- What's the value after eval?
- How does quote work on this?

If you can answer these, you're ready to dive deeper!

## Why This Matters

NbE is used in:
- **Coq**: Type checking and proof search
- **Agda**: Normalization and definitional equality
- **Lean**: Kernel type checker
- **Idris**: Evaluation and compilation

If you want to understand or build a proof assistant, you need NbE!

Good luck! You're about to learn one of the most elegant techniques in type theory! 🚀
