# Chapter 10: Linear Types - Quick Start

## TL;DR (30 seconds)

Linear types track resource usage at compile time. Linear values must be used exactly once - no duplication, no discarding. Think Rust ownership but in the type system! In 5 minutes, you'll write code that prevents resource leaks at compile time!

**Who**: Learners who completed Chapter 9 (Subtyping)
**Time**: 1-2 weeks (or 1 intensive week)
**Payoff**: Understanding Rust, safe resource management, session types

## What You'll Build

- Type checker with usage tracking
- Linear functions (use argument exactly once)
- Bang types (!) for unrestricted values
- Resource management patterns (files, memory)
- Understanding of linear vs affine vs unrestricted

**Tangible Outcome**: Write code where forgetting to close a file is a compile-time error!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-10-linear-types
stack build
stack exec linear-repl
```

You should see:
```
Welcome to the Linear Types REPL!
linear>
```

### Step 2: Your First Linear Function (1 minute)

```
linear> \x:1 Nat. x
  \x:1 Nat. x : Nat -o Nat
```

The `:1` means x is linear - must be used exactly once!

### Step 3: Try to Duplicate (1 minute)

```
linear> \x:1 Nat. (x, x)
  Type error: Linear variable x used more than once
```

Can't duplicate linear values!

### Step 4: Unrestricted Works (1 minute)

```
linear> \x:ω Nat. (x, x)
  \x:ω Nat. (x, x) : Nat -> Nat * Nat
```

The `:ω` means unrestricted - use as many times as you want!

## Your First Success - Resource Management (10 minutes)

Imagine a file handle that MUST be closed:

### 1. Define Linear File Operations (Conceptual)

```
open  : String -o Handle       -- Returns linear handle
close : Handle -o ()           -- Consumes handle
```

If you forget `close`, it's a type error!

### 2. Try Linear Identity

```
linear> \x:1 Nat. x
  \x:1 Nat. x : Nat -o Nat
```

Uses x exactly once. Perfect!

### 3. Try Linear Swap

```
linear> \p:1 (Nat * Bool). let (x, y) = p in (y, x)
  \p:1 (Nat * Bool). let (x, y) = p in (y, x) : (Nat * Bool) -o (Bool * Nat)
```

Both x and y used exactly once!

### 4. Try Bang for Duplication

```
linear> let !x = !5 in (x, x)
  (5, 5) : Nat * Nat
```

**Achievement Unlocked**: You just made a linear value unrestricted with bang!

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - step-by-step examples
2. Follow `LESSON_PLAN.md` - structured course
3. Use `REPL_GUIDE.md` when stuck
4. Try exercises 1-3 in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (30 minutes)
2. Study `CHEAT_SHEET.md` - usage rules
3. Work through exercises 1-5 (2-3 hours)
4. Take `QUIZ.md` to verify understanding

### For Explorers
1. Open `REPL_GUIDE.md` and try all examples
2. Experiment with linear vs unrestricted
3. Design resource management APIs
4. Compare with Rust ownership

## When to Skip This Chapter

**Skip if**:
- You already understand linear types deeply
- You've mastered Rust ownership semantics
- You just want basic type theory (but linear types are cool!)

**Don't skip if**:
- This is your first exposure to linear types
- You want to understand Rust's ownership
- You're interested in safe resource management
- You want to learn session types

## Quick Reference

```bash
# Build
cd chapter-10-linear-types && stack build

# Run REPL
stack exec linear-repl

# Run tests
stack test

# Essential REPL Commands
:help               # Show help
:type <expr>        # Show type of expression
:quit               # Exit

# Lambda Syntax with Multiplicities
\x:1 Nat. x                    # Linear lambda (exactly once)
\x:ω Nat. x                    # Unrestricted lambda (any times)
(e1, e2)                       # Pair (tensor product)
let (x, y) = e1 in e2          # Pair elimination
!e                             # Bang introduction
let !x = e1 in e2              # Bang elimination

# Types
Nat -o Nat                     # Linear function
Nat -> Nat                     # Unrestricted function
Nat * Bool                     # Pair type
!Nat                           # Bang type
```

## Key Concepts (3 minutes)

### Linear (1) vs Unrestricted (ω)

```
Linear :1       Use exactly once
Unrestricted :ω Use any number of times (0, 1, 2, ...)
```

### Examples

```
✓ \x:1 Nat. x              x used once
✗ \x:1 Nat. (x, x)         x used twice - ERROR!
✗ \x:1 Nat. 0              x not used - ERROR!

✓ \x:ω Nat. x              x used once - OK
✓ \x:ω Nat. (x, x)         x used twice - OK
✓ \x:ω Nat. 0              x not used - OK
```

### Context Splitting

In `(e1, e2)`, each linear variable goes to exactly one side:

```
✓ \x:1 Nat. \y:1 Bool. (x, y)    x left, y right
✗ \x:1 Nat. (x, x)                x can't be in both!
```

### Bang Type

`!A` makes a value unrestricted:

```
✓ !5                       OK: constants can be banged
✓ \x:ω Nat. !x             OK: unrestricted can be banged
✗ \x:1 Nat. !x             ERROR: can't bang linear!

✓ let !x = !5 in (x, x)    Unwrap to use multiple times
```

## Common Pitfalls (Avoid These!)

### Pitfall 1: Trying to Duplicate Linear

```
\x:1 Nat. (x, x)  ✗ WRONG
\x:ω Nat. (x, x)  ✓ CORRECT
```

### Pitfall 2: Trying to Discard Linear

```
\x:1 Nat. 0       ✗ WRONG
\x:ω Nat. 0       ✓ CORRECT
```

### Pitfall 3: Banging Linear Variables

```
\x:1 Nat. !x      ✗ WRONG
\x:ω Nat. !x      ✓ CORRECT
```

### Pitfall 4: Forgetting Pair Components

```
let (x, y) = p in x       ✗ WRONG (y unused)
let (x, y) = p in (x, y)  ✓ CORRECT
```

## Success Criteria

You're ready for Chapter 11 when you can:
- [ ] Understand linear vs unrestricted
- [ ] Use context splitting correctly
- [ ] Implement bang introduction/elimination
- [ ] Design resource management APIs
- [ ] Complete exercises 1-5

**Minimum**: Understand usage tracking and context splitting
**Ideal**: Complete all exercises and implement resource APIs

## Time Investment

- **Minimum**: 4 hours (basics only)
- **Recommended**: 8-12 hours (solid understanding)
- **Complete**: 20 hours (all exercises + deep exploration)

## Real-World Connections

### Rust Ownership

```rust
let file = File::open("data.txt")?;  // Linear ownership
let contents = read_file(file);      // file consumed
// file can't be used here - type error!
```

Linear types model Rust's ownership!

### Session Types

```
Send Int (Recv Bool End)
-- Must send Int, then receive Bool, then close
-- Protocol enforced at compile time!
```

### Safe Memory Management

```
malloc : Size -o Ptr
free   : Ptr -o ()

-- Must free exactly once!
```

## Interactive Examples

### Example 1: Linear Identity

```
linear> \x:1 Nat. x
  \x:1 Nat. x : Nat -o Nat

linear> (\x:1 Nat. x) 5
  5 : Nat
```

### Example 2: Linear Swap

```
linear> \p:1 (Nat * Bool). let (x, y) = p in (y, x)
  \p:1 (Nat * Bool). let (x, y) = p in (y, x) : (Nat * Bool) -o (Bool * Nat)

linear> (\p:1 (Nat * Bool). let (x, y) = p in (y, x)) (5, true)
  (true, 5) : Bool * Nat
```

### Example 3: Bang Duplication

```
linear> let !x = !5 in (x, x)
  (5, 5) : Nat * Nat

linear> \b:1 !Nat. let !x = b in (x, x)
  \b:1 !Nat. let !x = b in (x, x) : !Nat -o Nat * Nat
```

### Example 4: Unrestricted Function

```
linear> \x:ω Nat. if (iszero x) then x else (succ x)
  \x:ω Nat. if (iszero x) then x else (succ x) : Nat -> Nat
```

x is used in the condition AND both branches - needs unrestricted!

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md`
- **Need examples?** See `REPL_GUIDE.md`
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Reference**: `CHEAT_SHEET.md` for quick lookup
- **Practice**: `PRACTICE_PROBLEMS.md` for extra exercises

## Debugging Tips

### Issue: "Linear variable used more than once"

Check all uses of the variable:
```
\x:1 Nat. (x, x)  -- x appears twice!
```

Solution: Make it unrestricted or use bang.

### Issue: "Linear variable not used"

Every linear variable must be used:
```
\x:1 Nat. 0  -- x not used!
```

Solution: Make it unrestricted or actually use it.

### Issue: "Cannot bang linear variable"

You can only bang unrestricted values:
```
\x:1 Nat. !x  -- x is linear!
```

Solution: Make x unrestricted first.

### Issue: "Cannot split linear variable"

Linear variables can only be in one place:
```
\x:1 Nat. (x, x)  -- x in both sides of pair!
```

Solution: Use different variables or make it unrestricted.

## What Makes This Chapter Special

Linear types are about **resource management** in the type system. You'll learn:

- Usage tracking (exactly once vs any)
- Context splitting (linear variables can't be shared)
- Bang types (escaping linearity when needed)
- Resource patterns (file handles, memory, protocols)

These concepts underpin Rust, session types, and safe resource management.

## The Big Picture

```
Chapter 1-2  → Simple types
Chapter 3    → Products, sums, records
Chapter 9    → Subtyping (type relationships)
Chapter 10   → Linear types (usage tracking)  ← YOU ARE HERE
Future       → Session types, Rust ownership
```

Linear types add a new dimension: not just "what type?" but "how many times?"

## Resource Management Pattern

The key pattern with linear types:

```haskell
-- Open returns a linear handle
open : Path -o Handle

-- Operations thread the handle through
read : Handle -o (Data * Handle)

-- Close consumes the handle
close : Handle -o ()

-- Usage:
let h = open "file.txt" in
let (data, h') = read h in
close h'
```

Can't forget to close - it's a type error!

## Comparison with Other Systems

| System | Discard? | Duplicate? | Example |
|--------|----------|------------|---------|
| **Linear** (1) | No | No | This chapter |
| **Affine** (≤1) | Yes | No | Rust ownership |
| **Relevant** (≥1) | No | Yes | - |
| **Unrestricted** (ω) | Yes | Yes | Normal types |

## Ready?

```bash
cd chapter-10-linear-types
stack build
stack exec linear-repl
```

Type your first command:
```
linear> \x:1 Nat. x
```

Let's go! You're about to understand how Rust's ownership system works at the type level!

## Quick Win

Try this 3-minute exercise:

```
linear> -- 1. Linear identity
linear> \x:1 Nat. x

linear> -- 2. Try to duplicate (fails!)
linear> \x:1 Nat. (x, x)

linear> -- 3. Unrestricted duplication (works!)
linear> \x:ω Nat. (x, x)

linear> -- 4. Bang to make unrestricted
linear> let !x = !5 in (x, x)
```

You just learned the core of linear types!
