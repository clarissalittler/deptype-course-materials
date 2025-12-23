# Chapter 9: Subtyping - Quick Start

## TL;DR (30 seconds)

Subtyping lets you use more specific types where more general types are expected. Key insight: `{x: Nat, y: Bool} <: {x: Nat}` (more fields = subtype), and function arguments are contravariant (direction flips!). In 5 minutes, you'll understand when one type can substitute for another!

**Who**: Learners who completed Chapter 3 (STLC with ADTs)
**Time**: 1-2 weeks (or 1 intensive week)
**Payoff**: Foundation for OOP, TypeScript, and type-safe polymorphism

## What You'll Build

- Type checker with subtyping (Top, Bot, records)
- Understanding of width/depth subtyping
- Function variance (contravariant arguments!)
- Join/meet for combining types
- Type-safe upcasting via ascription

**Tangible Outcome**: Type check code where `ColoredPoint` works wherever `Point` is expected!

## 5-Minute Setup

### Step 1: Build and Run (2 minutes)

```bash
cd chapter-09-subtyping
stack build
stack exec subtyping-repl
```

You should see:
```
Welcome to the Subtyping REPL!
subtype>
```

### Step 2: Your First Subtype Check (1 minute)

```
subtype> :subtype Bool Top
  Bool <: Top ✓
```

Congrats! Every type is a subtype of Top!

### Step 3: Width Subtyping (1 minute)

```
subtype> :subtype {x: Nat, y: Bool} {x: Nat}
  {x: Nat, y: Bool} <: {x: Nat} ✓
```

Records with MORE fields are subtypes! This is the key insight.

### Step 4: Function Contravariance (1 minute)

```
subtype> :subtype (Top -> Nat) (Bool -> Nat)
  (Top -> Nat) <: (Bool -> Nat) ✓
```

Arguments are contravariant - the direction flips!

## Your First Success - Record Subtyping (10 minutes)

Follow this mini-tutorial to cement your understanding:

### 1. Define a Point Type

```
subtype> :type {x = 0, y = 0}
  {x: Nat, y: Nat}
```

### 2. Define a Function Using Points

```
subtype> let getX = \p:{x: Nat}. p.x
subtype> :type getX
  {x: Nat} -> Nat
```

### 3. Apply to a Colored Point

```
subtype> getX {x = 5, y = 10, color = true}
  5
```

It works! `{x: Nat, y: Nat, color: Bool} <: {x: Nat}`

### 4. Try Contravariance

```
subtype> let acceptTop = \x:Top. 0
subtype> let useFunc = \f:(Bool -> Nat). f true
subtype> useFunc acceptTop
  0
```

**Achievement Unlocked**: You just used contravariance! `Top -> Nat <: Bool -> Nat` because `Bool <: Top`.

## Next Steps

Choose your path:

### For Complete Beginners
1. Read `TUTORIAL.md` (60-90 minutes) - step-by-step examples
2. Follow `LESSON_PLAN.md` - structured course
3. Use `REPL_GUIDE.md` when stuck
4. Try exercises 1-3 in `exercises/EXERCISES.md`

### For Quick Learners
1. Skim `README.md` - formal semantics (30 minutes)
2. Study `CHEAT_SHEET.md` - variance rules
3. Work through exercises 1-6 (2-3 hours)
4. Take `QUIZ.md` to verify understanding

### For Explorers
1. Open `REPL_GUIDE.md` and try all examples
2. Experiment with `:subtype` command
3. Design your own class hierarchies with records
4. Explore join and meet operations

## When to Skip This Chapter

**Skip if**:
- You already understand subtyping deeply
- You've mastered TypeScript/Flow structural typing
- You just want dependent types (but subtyping helps!)

**Don't skip if**:
- This is your first exposure to subtyping
- You want to understand OOP type systems
- You're confused by TypeScript's structural typing
- You want to learn about variance

## Quick Reference

```bash
# Build
cd chapter-09-subtyping && stack build

# Run REPL
stack exec subtyping-repl

# Run tests
stack test

# Essential REPL Commands
:help               # Show help
:type <expr>        # Show type of expression
:subtype T1 T2      # Check if T1 <: T2
:quit               # Exit

# Lambda Syntax
\x:Nat. x                    # Typed lambda
{x = 0, y = true}            # Record
{x = 0, y = true}.x          # Projection
(e as {x: Nat})              # Ascription (upcast)

# Subtyping Checks
:subtype Bool Top            # Every type <: Top
:subtype Bot Nat             # Bot <: every type
:subtype {x: Nat, y: Bool} {x: Nat}  # Width subtyping
```

## Key Concepts (3 minutes)

### Width Subtyping
**More fields = subtype**

```
{x: Nat, y: Bool, z: Top} <: {x: Nat, y: Bool} <: {x: Nat}
```

Think: "A colored point can do everything a point can."

### Function Contravariance
**Arguments flip direction**

```
If Dog <: Animal, then:
  (Animal -> String) <: (Dog -> String)  ✓
  (Dog -> String) <: (Animal -> String)  ✗
```

Think: "A function that handles ANY animal can handle dogs."

### Top and Bot
```
        Top (everything goes here)
       / | \
     ... ... ...
       \ | /
        Bot (never has values)
```

### Join (Least Upper Bound)
```
{x: Nat, y: Bool} ⊔ {x: Nat, z: Top} = {x: Nat}
```

Only common fields survive!

## Success Criteria

You're ready for Chapter 10 when you can:
- [ ] Explain width and depth subtyping
- [ ] Understand function contravariance
- [ ] Use Top and Bot correctly
- [ ] Compute joins and meets
- [ ] Complete exercises 1-5

**Minimum**: Understand width subtyping and contravariance
**Ideal**: Complete all exercises and implement algorithmic subtyping

## Time Investment

- **Minimum**: 4 hours (basics only)
- **Recommended**: 8-12 hours (solid understanding)
- **Complete**: 20 hours (all exercises + deep exploration)

## Common Pitfalls (Avoid These!)

### Pitfall 1: Width Direction
```
{x: Nat} <: {x: Nat, y: Bool}  ✗ WRONG
{x: Nat, y: Bool} <: {x: Nat}  ✓ CORRECT
```

### Pitfall 2: Contravariance
```
(Dog -> R) <: (Animal -> R)    ✗ WRONG (if Dog <: Animal)
(Animal -> R) <: (Dog -> R)    ✓ CORRECT
```

### Pitfall 3: Join Loses Fields
```
if b then {x = 0, y = true} else {x = 1, z = false}
-- Type: {x: Nat}, NOT {x: Nat, y: Bool, z: Bool}
```

## Real-World Connections

### TypeScript
```typescript
interface Point { x: number; y: number }
function getX(p: Point) { return p.x; }
getX({ x: 0, y: 0, color: "red" });  // Works! Width subtyping
```

### Scala
```scala
class List[+A]  // Covariant: List[Dog] <: List[Animal]
```

### Java (Broken!)
```java
String[] strings = new String[1];
Object[] objects = strings;  // Allowed (covariant arrays)
objects[0] = 42;             // Runtime error! Unsound!
```

## Interactive Examples

### Example 1: OOP Class Hierarchy
```
subtype> let animal = {name = "generic"}
subtype> let dog = {name = "Fido", breed = "Labrador"}
subtype> let getDogName = \d:{name: Bool, breed: Bool}. d.name
subtype> :type getDogName

-- Can we pass 'dog' to a function expecting 'animal'?
subtype> :subtype {name: Bool, breed: Bool} {name: Bool}
  ✓

-- Yes! Width subtyping
```

### Example 2: Contravariance in Action
```
subtype> let feedAnimal = \a:Top. ()
subtype> let registerDogFeeder = \f:(Bool -> ()). f true

subtype> registerDogFeeder feedAnimal
-- Works because Top -> () <: Bool -> ()
```

### Example 3: Join for Conditionals
```
subtype> if true then {x = 0, shared = true} else {shared = false, y = 0}
-- Type: {shared: Bool}  (only common field!)
```

## Help & Resources

- **Stuck?** Check `COMMON_MISTAKES.md`
- **Need examples?** See `REPL_GUIDE.md`
- **Want structure?** Follow `LESSON_PLAN.md`
- **Test yourself**: Take `QUIZ.md`
- **Reference**: `CHEAT_SHEET.md` for quick lookup
- **Practice**: `PRACTICE_PROBLEMS.md` for extra exercises

## Debugging Tips

### Issue: Subtyping check fails
1. Check direction: more specific <: more general
2. For records: more fields <: fewer fields
3. For functions: flip arguments, same results

### Issue: Type error in application
1. Does argument type match parameter?
2. Is argument a subtype of parameter?
3. Remember: subtyping is checked, not inferred

### Issue: Join gives unexpected type
1. Join keeps only common fields/structure
2. For functions: meet args, join results
3. If no join exists, result is Top

## What Makes This Chapter Special

Unlike previous chapters, subtyping is about **relationships between types**, not just typing individual terms. You'll learn to think about:

- Type hierarchies (lattices)
- Variance (covariant, contravariant, invariant)
- Substitutability (Liskov Substitution Principle)
- Type-safe upcasting

These concepts underpin modern type systems (TypeScript, Scala, Kotlin) and OOP.

## The Big Picture

```
Chapter 1-2  → Simple types (no relationships)
Chapter 3    → Products, sums, records
Chapter 9    → Subtyping (type relationships!)  ← YOU ARE HERE
Chapter 10   → Linear types (usage tracking)
Future       → Bounded quantification (∀α <: T. τ)
```

Subtyping bridges simple type systems and advanced polymorphism!

## Ready?

```bash
cd chapter-09-subtyping
stack build
stack exec subtyping-repl
```

Type your first command:
```
subtype> :subtype {x: Nat, y: Bool} {x: Nat}
```

Let's go! You're about to understand how TypeScript, Scala, and OOP languages actually work under the hood!
