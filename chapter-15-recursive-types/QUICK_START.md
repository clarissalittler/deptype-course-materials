# Chapter 15: Recursive Types (μ Types) - Quick Start

## TL;DR (30 seconds)

Recursive types let types refer to themselves, enabling data structures like lists and trees. The μ (mu) operator creates recursive types, and fold/unfold operations convert between the recursive type and its unfolded form. In 5 minutes, you'll build your first recursive list!

**Who**: Anyone comfortable with STLC and algebraic data types
**Time**: 1-2 weeks (or 3-4 intensive days)
**Payoff**: Understand how lists, trees, and infinite structures are typed

## What You'll Build

- Lists using recursive types
- Binary trees
- Streams (infinite data)
- Understanding of fold/unfold operations
- Connection between recursion and fixed points

**Tangible Outcome**: Type-safe recursive data structures from scratch!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-15-recursive-types
stack build
stack exec recursive-repl
```

You should see:
```
Welcome to the Recursive Types REPL!
recursive>
```

### Step 2: Your First Recursive Type (1 minute)

```
recursive> :t mu a. Unit + a
μa. Unit + a
```

Congrats! You just wrote a recursive type for optional values!

### Step 3: The List Type (1 minute)

```
recursive> :def NatList = mu a. Unit + (Nat × a)
Defined: NatList

recursive> :t NatList
μa. Unit + (Nat × a)
```

This is a list of natural numbers!

### Step 4: Creating a List (1 minute)

```
recursive> :def nil = fold [NatList] (inl unit)
Defined: nil

recursive> :t nil
NatList
```

You just created an empty list using fold!

## Your First Success - Building Lists (10 minutes)

Follow this mini-tutorial to cement your understanding:

### 1. Define the List Type
```
recursive> :def NatList = mu a. Unit + (Nat × a)
```

Read this as: "A list is either empty (Unit) or a number paired with more list (a)"

### 2. Create Empty List
```
recursive> :def nil = fold [NatList] (inl unit)
recursive> :t nil
NatList
```

The `fold` wraps the unfolded type into the recursive type.

### 3. Create Cons (Add to Front)
```
recursive> :def cons = \n:Nat. \l:NatList.
             fold [NatList] (inr <n, l>)
recursive> :t cons
Nat → NatList → NatList
```

### 4. Build a List
```
recursive> cons 1 (cons 2 (cons 3 nil))
fold [NatList] (inr <1, fold [NatList] (inr <2, fold [NatList] (inr <3, ...>)>)>)
```

### 5. Check if Empty
```
recursive> :def isEmpty = \l:NatList.
             case unfold [NatList] l of
               inl _ => true
             | inr _ => false

recursive> isEmpty nil
true

recursive> isEmpty (cons 1 nil)
false
```

**Achievement Unlocked**: You just built type-safe lists from scratch!

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - step-by-step walkthrough
2. Follow `LESSON_PLAN.md` - structured 12-16 hour course
3. Use `REPL_GUIDE.md` when stuck
4. Try exercises 1-5 in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (30 minutes)
2. Read key sections: Iso-recursive, fold/unfold
3. Work through exercises 1-10 (2-3 hours)
4. Take `QUIZ.md` to verify understanding

### For Explorers
1. Open `REPL_GUIDE.md` and try all examples
2. Implement your own data structures
3. Explore streams and infinite data
4. Build the Y combinator with recursive types

## When to Skip This Chapter

**Skip if**:
- You already understand μ types deeply
- You've worked through TAPL Chapter 20
- You just want to learn about HoTT (but μ is foundational!)

**Don't skip if**:
- This is your first exposure to recursive types
- You want to understand how lists/trees are typed
- You're building up to dependent types

## Quick Reference

```bash
# Build
cd chapter-15-recursive-types && stack build

# Run REPL
stack exec recursive-repl

# Essential REPL Commands
:help               # Show help
:def name = term    # Save a definition
:t term             # Show type
:eval term          # Evaluate term
:quit               # Exit

# Recursive Type Syntax
mu a. T             # Recursive type
fold [T] t          # Wrap into recursive type
unfold [T] t        # Unwrap from recursive type

# Your First Definitions
:def NatList = mu a. Unit + (Nat × a)
:def nil = fold [NatList] (inl unit)
:def cons = \n:Nat. \l:NatList. fold [NatList] (inr <n, l>)
```

## The Key Insight

### The Problem
```
List Nat = ???
-- A list is either empty OR a Nat followed by... another list!
-- How do we refer to "List" in its own definition?
```

### The Solution
```
NatList = μa. Unit + (Nat × a)
--        ^^         ^^^^   ^
--        |          |      α refers back to NatList
--        |          empty case
--        binds a
```

### The Operations
```
fold   : T[μa.T/a] → μa.T       -- Wrap up
unfold : μa.T → T[μa.T/a]       -- Unwrap to examine
```

## Success Criteria

You're ready for Chapter 16 when you can:
- [ ] Define recursive types with μ
- [ ] Use fold to create values
- [ ] Use unfold to examine values
- [ ] Encode lists and trees
- [ ] Complete exercises 1-5

**Minimum**: Understand fold/unfold and can build lists
**Ideal**: Complete all exercises and understand fixed points

## Time Investment

- **Minimum**: 6 hours (basics only)
- **Recommended**: 12-16 hours (solid understanding)
- **Complete**: 25 hours (all exercises + deep exploration)

## Common Gotchas

### Gotcha 1: Forgetting fold
```
-- WRONG
nil : NatList
nil = inl unit    -- Type error!

-- RIGHT
nil = fold [NatList] (inl unit)
```

### Gotcha 2: Forgetting unfold
```
-- WRONG
isEmpty = \l:NatList.
  case l of ...    -- Can't match on recursive type!

-- RIGHT
isEmpty = \l:NatList.
  case unfold [NatList] l of ...
```

### Gotcha 3: Wrong type annotation
```
-- WRONG
fold [Unit + (Nat × NatList)] ...

-- RIGHT
fold [NatList] ...
-- or
fold [mu a. Unit + (Nat × a)] ...
```

## Practical Examples

### Lists
```
NatList = μa. Unit + (Nat × a)
nil = fold [NatList] (inl unit)
cons = \n. \l. fold [NatList] (inr <n, l>)
```

### Binary Trees
```
Tree = μa. Nat + (a × a)
leaf = \n. fold [Tree] (inl n)
branch = \l. \r. fold [Tree] (inr <l, r>)
```

### Streams
```
Stream = μa. Nat × a
head = \s. fst (unfold [Stream] s)
tail = \s. snd (unfold [Stream] s)
```

## The Bigger Picture

### Connection to Fixed Points
```
μa. T  is the least fixed point of λa. T
```

If F is a type operator, then:
```
μa. F(a) ≅ F(μa. F(a))
```

### Enables General Recursion
```
SelfApp = μa. a → Nat
omega = \x:SelfApp. (unfold [SelfApp] x) x
```

This breaks strong normalization - we can write infinite loops!

### Path Forward
- Recursive types are the foundation for inductive types
- Lead to dependent types (Chapter 7-8)
- Connect to coinductive types for infinite data
- Enable general recursion at the type level

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md`
- **Need examples?** See `REPL_GUIDE.md`
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Reference**: `CHEAT_SHEET.md` for quick lookup

## Motivation: Why μ Types?

### Without Recursive Types
```
-- Can't define this in STLC!
data List a = Nil | Cons a (List a)
```

### With Recursive Types
```
List a = μb. Unit + (a × b)
-- Self-reference achieved!
```

### What You Can Build
- Lists, trees, graphs
- Infinite streams
- The Y combinator (general recursion)
- Self-applicable functions
- Any inductive/coinductive data type

## Debugging Checklist

When things go wrong:

1. **Type mismatch on creation**: Add `fold`
2. **Can't pattern match**: Add `unfold`
3. **Wrong annotation**: Use `μa.T` not unfolded form
4. **Infinite loop**: Recursive types allow non-termination
5. **Confused about iso/equi**: We use iso-recursive (need fold/unfold)

## Final Tips

1. **Think in two levels**: The recursive type vs its unfolded form
2. **Remember the pattern**: fold to create, unfold to examine
3. **Visualize the structure**: Draw out the data structure
4. **Connect to familiar**: Lists = nil | cons, Trees = leaf | branch
5. **Embrace recursion**: μ is the essence of self-reference

Good luck! You're about to master one of the most powerful type system features!
