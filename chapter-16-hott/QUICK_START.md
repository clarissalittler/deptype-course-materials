# Chapter 16: Homotopy Type Theory - Quick Start

## TL;DR (30 seconds)

Homotopy Type Theory (HoTT) reinterprets types as spaces and equalities as paths. Instead of equality being true/false, it's a type of paths between points! This geometric view revolutionizes how we think about equality and enables powerful new principles like univalence. In 5 minutes, you'll work with your first paths!

**Who**: Anyone with dependent types background (Chapter 7-8)
**Time**: 2-3 weeks (or 1 intensive week for basics)
**Payoff**: Revolutionary perspective on equality and types

## What You'll Build

- Understanding of identity types as paths
- Mastery of path operations (sym, trans, ap, transport)
- Grasp of the J eliminator (path induction)
- Appreciation of higher groupoid structure
- Conceptual understanding of univalence

**Tangible Outcome**: Work with paths at all levels - paths between points, paths between paths, and beyond!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-16-hott
stack build
stack exec hott-repl
```

You should see:
```
Welcome to the HoTT REPL!
hott>
```

### Step 2: Your First Path (1 minute)

```
hott> refl [Nat] 0
refl [Nat] 0

hott> :t refl [Nat] 0
Id Nat 0 0
```

Congrats! You just created a path from 0 to itself!

### Step 3: Path Operations (1 minute)

```
hott> sym (refl [Nat] 0)
refl [Nat] 0

hott> trans (refl [Nat] 0) (refl [Nat] 0)
refl [Nat] 0
```

Paths compose and reverse!

### Step 4: Functions Preserve Paths (1 minute)

```
hott> ap (\x:Nat. succ x) (refl [Nat] 3)
refl [Nat] (succ 3)

hott> :t ap (\x:Nat. succ x) (refl [Nat] 3)
Id Nat (succ 3) (succ 3)
```

Functions map paths to paths!

## Your First Success - Path Algebra (10 minutes)

Follow this mini-tutorial to understand paths:

### 1. The Identity Type
```
hott> :t Id Nat 5 5
Type

hott> :t refl [Nat] 5
Id Nat 5 5
```

`Id Nat 5 5` is the TYPE of paths from 5 to 5. `refl` is one such path!

### 2. Symmetry (Path Reversal)
```
hott> :def p = refl [Nat] 7
Defined: p

hott> :t sym p
Id Nat 7 7

hott> sym p
refl [Nat] 7
```

Reversing a trivial path gives the same trivial path.

### 3. Transitivity (Path Composition)
```
hott> :def q = refl [Nat] 7
hott> trans p q
refl [Nat] 7
```

Composing paths walks both paths in sequence.

### 4. Action on Paths (ap)
```
hott> :def f = \x:Nat. succ x
hott> ap f (refl [Nat] 5)
refl [Nat] (succ 5)
```

Functions are "continuous" - they preserve paths!

### 5. Transport
```
hott> transport (\x:Bool. Nat) (refl [Bool] true) (succ 0)
succ 0
```

Transport moves data along paths.

**Achievement Unlocked**: You understand the basic path operations!

## The Big Insight

### Traditional View
```
a = b    -- Either true or false
```

### HoTT View
```
Id A a b    -- A TYPE of paths from a to b
            -- Could have 0, 1, or many paths!
```

### Why This Matters

In topology, there can be different paths between the same points:

```
     ___p___
    /       \
   a         b
    \_______/
        q
```

In HoTT, `p` and `q` might be different elements of `Id A a b`!

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (90-120 minutes) - gentle introduction
2. Follow `LESSON_PLAN.md` - structured 16-20 hour course
3. Use `REPL_GUIDE.md` when experimenting
4. Try exercises 1-5 in `exercises/EXERCISES.md`

### For Quick Learners
1. Read `README.md` - formal foundations (45 minutes)
2. Focus on: J eliminator, path operations, groupoid laws
3. Work through exercises 1-10 (3-4 hours)
4. Take `QUIZ.md` to verify understanding

### For Explorers
1. Open `REPL_GUIDE.md` and try all examples
2. Experiment with higher paths
3. Think about univalence implications
4. Explore the circle and other HITs conceptually

## When to Skip This Chapter

**Skip if**:
- You're already familiar with HoTT basics
- You've studied the HoTT Book
- You want to focus on practical type systems first

**Don't skip if**:
- This is your first exposure to HoTT
- You want to understand modern foundations of mathematics
- You're curious about cubical type theory

## Quick Reference

```bash
# Build
cd chapter-16-hott && stack build

# Run REPL
stack exec hott-repl

# Essential REPL Commands
:help               # Show help
:t term             # Show type
:def name = term    # Save definition
:eval term          # Evaluate
:quit               # Exit

# Path Syntax
refl [A] a          # Reflexivity path
sym p               # Path inverse
trans p q           # Path composition
ap f p              # Apply function to path
transport P p x     # Transport along path

# Your First Paths
:t refl [Nat] 0                    # Id Nat 0 0
:t sym (refl [Nat] 5)              # Id Nat 5 5
:t trans (refl [Nat] 0) (refl [Nat] 0)  # Id Nat 0 0
```

## The Key Concepts

### 1. Types as Spaces
```
Bool = {true, false}    -- Two discrete points
Nat = {0, 1, 2, ...}    -- Discrete space
```

### 2. Paths Between Points
```
refl [Nat] 0 : Id Nat 0 0
-- The trivial path from 0 to itself
```

### 3. The J Eliminator
```
J : To prove something for all paths,
    prove it for refl!
```

This is path induction - the fundamental principle.

### 4. Derived Operations
All path operations come from J:
- `sym` - reverse paths
- `trans` - compose paths
- `ap` - apply functions
- `transport` - lift along paths

### 5. Higher Structure
```
1-paths: between points
2-paths: between 1-paths
3-paths: between 2-paths
...
∞-groupoid structure!
```

## Success Criteria

You're ready to move on when you can:
- [ ] Explain types as spaces, terms as points
- [ ] Use refl to create paths
- [ ] Apply sym, trans, ap, transport
- [ ] Understand the J eliminator conceptually
- [ ] Complete exercises 1-5

**Minimum**: Understand basic path operations
**Ideal**: Complete exercises and understand groupoid laws

## Time Investment

- **Minimum**: 8 hours (basics only)
- **Recommended**: 16-20 hours (solid understanding)
- **Complete**: 30+ hours (all exercises + HoTT Book reading)

## Common Gotchas

### Gotcha 1: Paths are types!
```
-- WRONG THINKING
a = b is true or false

-- RIGHT THINKING
Id A a b is a TYPE
It has elements (paths)
There can be many different paths!
```

### Gotcha 2: J only computes on refl
```
J C base a a refl = base a    ✓ Computes

J C base a b p = ???          ✗ Stuck (if p ≠ refl)
```

### Gotcha 3: Endpoints must match
```
trans p q
-- p : Id A a b
-- q : Id A c d    ✗ WRONG (b ≠ c)
-- q : Id A b c    ✓ RIGHT
```

## Practical Examples

### Symmetry
```
sym : Id A a b → Id A b a

-- Reverses direction
p : Id Nat 1 2
sym p : Id Nat 2 1
```

### Transitivity
```
trans : Id A a b → Id A b c → Id A a c

-- Composes paths
p : Id Nat 1 2
q : Id Nat 2 3
trans p q : Id Nat 1 3
```

### ap (Functoriality)
```
ap : (f : A → B) → Id A a b → Id B (f a) (f b)

-- Functions preserve paths
f = λx. succ x
p : Id Nat 0 0
ap f p : Id Nat (succ 0) (succ 0)
```

### Transport
```
transport : (P : A → Type) → Id A a b → P a → P b

-- Move data along paths
P = λ_:Bool. Nat
p : Id Bool true true
transport P p 5 : Nat  -- equals 5
```

## The Bigger Picture

### Groupoid Laws
Paths satisfy algebraic laws (but these are themselves paths!):

```
trans refl p = p             -- Left identity
trans p refl = p             -- Right identity
trans p (sym p) = refl       -- Inverse
trans (trans p q) r =
  trans p (trans q r)        -- Associativity
```

### Univalence (Conceptual)
```
(A ≃ B) ≃ (A = B)

-- Equivalent types are equal!
-- Isomorphic structures can be identified!
```

### Higher Inductive Types
Types with path constructors:

```
-- The circle
S¹ has:
  - base : S¹               (point)
  - loop : Id S¹ base base  (path!)
```

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md`
- **Need examples?** See `REPL_GUIDE.md`
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Reference**: `CHEAT_SHEET.md` for quick lookup
- **Deep dive**: The HoTT Book (free online)

## Motivation: Why HoTT?

### 1. Unifies Logic and Topology
```
Type theory ↔ Homotopy theory
Types ↔ Spaces
Paths ↔ Homotopies
```

### 2. Powerful Principles
- Univalence: equivalent types are equal
- Function extensionality: pointwise equal functions are equal
- Higher inductive types: specify spaces by their structure

### 3. Foundations of Mathematics
HoTT provides an alternative foundation to set theory, with:
- Constructive proofs
- Computational content
- Geometric intuition

### 4. Practical Applications
- Proof assistants: Agda --cubical, Arend
- Verified mathematics
- Program equivalence

## Path Forward

After mastering basic HoTT:

1. **Cubical Type Theory**: Computational univalence
2. **The HoTT Book**: Complete treatment
3. **Proof Assistants**: Agda, Lean, Coq
4. **Synthetic Homotopy Theory**: Prove topology in type theory

## Debugging Checklist

When things go wrong:

1. **Type error on sym**: Check if endpoints reverse correctly
2. **Type error on trans**: Ensure middle points match
3. **J doesn't compute**: Only computes on refl!
4. **Confused about higher paths**: Draw a diagram
5. **Need UIP**: You're not in HoTT! HoTT rejects UIP

## Final Tips

1. **Think geometrically**: Visualize types as spaces
2. **Draw diagrams**: Paths, compositions, higher paths
3. **Start simple**: Master refl before higher paths
4. **Use J**: It's the fundamental principle
5. **Be patient**: HoTT is a paradigm shift!

## The Revolutionary Insight

```
Traditional: a = b is a proposition
HoTT: a = b is a TYPE of paths

This changes everything!
```

Good luck on your journey into Homotopy Type Theory!
