# Chapter 17: Abstract Machines - Quick Start

## TL;DR (30 seconds)

Abstract machines make evaluation explicit by using **environments** (variable lookup tables) and **continuations** (control flow stacks) instead of slow substitution. This chapter implements three classic machines: CEK (call-by-value), SECD (compiled bytecode), and Krivine (lazy). In 5 minutes, you'll trace your first abstract machine execution!

**Who**: Students with lambda calculus background (Chapter 1)
**Time**: 1-2 weeks
**Payoff**: Understanding how interpreters and VMs really work

## What You'll Build

- CEK machine with explicit continuations
- SECD machine with bytecode compilation
- Krivine machine for lazy evaluation
- Understanding of closures, environments, and control flow

**Tangible Outcome**: Run factorial in three different evaluation strategies!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-17-abstract-machines
stack build
stack exec abstract-machines-repl
```

You should see:
```
Abstract Machines REPL
am>
```

### Step 2: Your First Evaluation (1 minute)

```
am> (\x. x) 5
Result: 5
```

The identity function applied to 5!

### Step 3: See the Machine (1 minute)

```
am> :trace (\x. x) 5
CEK trace (5 steps):
  Eval ((\x. x) 5) env={} kont=[]
  Eval (\x. x) env={} kont=[FApp1 5 {}]
  Apply kont=[FApp1 5 {}] val=<λx.x, {}>
  Eval 5 env={} kont=[FApp2 <λx.x, {}>]
  Apply kont=[FApp2 <λx.x, {}>] val=5
  Eval x env={x→5} kont=[]
  Apply kont=[] val=5
Result: 5
```

You just saw the CEK machine in action!

### Step 4: Compare Machines (1 minute)

```
am> :machine krivine
Switched to Krivine machine

am> (\x. 42) error
Result: 42

am> :machine cek
Switched to CEK machine

am> (\x. 42) error
Error: undefined variable
```

See the difference? Krivine (lazy) never evaluates `error`!

## Your First Success - Closures (10 minutes)

### Understanding Closures

A closure captures its environment:

```
am> let y = 10 in \x. x + y
Result: <λx. x+y, {y→10}>
```

### 1. Define a Function in Context

```
am> let x = 5 in (\y. x + y)
Result: <λy. x+y, {x→5}>
```

The lambda "closed over" the binding `x = 5`!

### 2. Apply the Closure

```
am> let x = 5 in ((\y. x + y) 3)
Result: 8
```

It remembered `x = 5` and added it to `y = 3`.

### 3. Nested Closures

```
am> let x = 1 in let f = \y. x + y in let x = 100 in f 5
Result: 6
```

`f` captured the **first** `x = 1`, not the second `x = 100`. This is lexical scoping!

**Achievement Unlocked**: You understand closures!

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (90 minutes) - step-by-step examples
2. Follow `LESSON_PLAN.md` - structured course
3. Use `REPL_GUIDE.md` when experimenting
4. Try exercises 1-3 in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (30 minutes)
2. Work through exercises 1-7 (3-4 hours)
3. Compare CEK, SECD, and Krivine traces
4. Take `QUIZ.md` to verify understanding

### For Implementers
1. Study CEK implementation in `src/CEK.hs`
2. Implement your own SECD machine
3. Add new features (pairs, exceptions, state)
4. Use `:step` mode to debug

## When to Skip This Chapter

**Skip if**:
- You already understand abstract machines
- You've implemented interpreters with environments
- You just want type theory (skip to later chapters)

**Don't skip if**:
- First time with environments and closures
- Want to understand how interpreters work
- Planning to implement your own language
- Interested in evaluation strategies

## Quick Reference

```bash
# Build
cd chapter-17-abstract-machines && stack build

# Run REPL
stack exec abstract-machines-repl

# REPL Commands
:help                # Show help
:machine cek         # Switch to CEK
:machine secd        # Switch to SECD
:machine krivine     # Switch to Krivine
:trace <term>        # Show full trace
:step <term>         # Step-by-step mode
:quit                # Exit

# Syntax
\x. x                # Lambda
(\x. x) 5            # Application
let x = 5 in x + 1   # Let binding
if0 n then t else f  # Conditional
```

## Interactive Examples

### Example 1: CEK Evaluation

```
am> :machine cek
am> :trace ((\f. \x. f x) (\y. y + 1) 0)

See how:
1. Function is evaluated first
2. Argument is evaluated next
3. Closures capture environments
4. Continuation tracks "what's next"
```

### Example 2: SECD Compilation

```
am> :machine secd
am> :compile \x. x + 1

Instructions:
  IClosure [IAccess 0, IConst 1, IAdd, IReturn]

am> :trace ((\x. x + 1) 5)

See the stack-based execution!
```

### Example 3: Krivine Laziness

```
am> :machine krivine
am> :trace (\x. \y. x) 5 expensive

Notice:
1. Arguments pushed as thunks
2. 'expensive' never evaluated
3. Result is 5 immediately
```

## Success Criteria

You're ready for Chapter 18 when you can:
- [ ] Explain the difference between substitution and environments
- [ ] Trace a simple term through CEK
- [ ] Understand closures and environment capture
- [ ] Explain call-by-value vs call-by-name
- [ ] Complete exercises 1-5

**Minimum**: Understand CEK machine and closures
**Ideal**: Trace all three machines and understand their differences

## Time Investment

- **Minimum**: 6 hours (CEK only)
- **Recommended**: 12-16 hours (all three machines)
- **Complete**: 24 hours (all exercises + extensions)

## Common First Questions

### Q: Why not just use substitution?

**A:** Substitution is slow (O(n) per substitution) and copies large terms. Environments are O(1) to extend and share structure.

### Q: What's the point of different machines?

**A:** Different evaluation strategies and implementation techniques:
- CEK: Simple, explicit control
- SECD: Compiled to bytecode
- Krivine: Lazy evaluation

### Q: Are these used in real systems?

**A:** Yes! CEK-like: JavaScript, Python. SECD-like: OCaml, Java. Krivine-like: Haskell (GHC).

## Visual Aid: CEK State Transitions

```
              ┌─────────────┐
              │ Eval t ρ κ  │
              └──────┬──────┘
                     │
        ┌────────────┼────────────┐
        │                         │
   If t is value              If t needs eval
        │                         │
        ▼                         ▼
  ┌───────────┐           ┌──────────────┐
  │ Apply κ v │           │ Push frame,  │
  └─────┬─────┘           │ eval subterm │
        │                 └──────┬───────┘
        │                        │
   Pop frame                     │
   Continue                 ┌────┘
        │                   │
        └───────────────────┘
```

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md`
- **Need examples?** See `REPL_GUIDE.md`
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Quick lookup**: `CHEAT_SHEET.md`

## Pro Tips

1. **Use :trace liberally**: See exactly what the machine does
2. **Compare machines**: Run same term in CEK, SECD, Krivine
3. **Start simple**: Master identity and const before complex terms
4. **Draw pictures**: Sketch environment and continuation on paper
5. **Use :step mode**: Step through evaluation manually

## First Exercise

Try this before moving on:

```
am> :trace ((\x. \y. x) 5 10)
```

Questions:
- When is the closure for `\y. x` created?
- What environment does it capture?
- Is 10 ever evaluated?

If you can answer these, you're ready to dive deeper!

Good luck! You're about to understand how computation actually happens! 🚀
