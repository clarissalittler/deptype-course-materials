# Chapter 9: Subtyping - Tutorial

This tutorial walks through subtyping concepts with step-by-step examples.

## Part 1: What is Subtyping?

### The Core Idea

Subtyping answers the question: "When can I use type S where type T is expected?"

If `S <: T` (read "S is a subtype of T"), then:
- Any value of type S can be safely used as a value of type T
- S is "at least as good as" T
- S is more specific, T is more general

### A Real-World Analogy

Think of job requirements:
- Job posting wants: "Someone who can code"
- Candidate has: "Coding + design + management skills"

The candidate is a "subtype" - they have all required skills plus more!

### The Subtype Lattice

```
            Top (most general)
           / | \
        Bool Nat {x:τ}...
           \ | /
            Bot (most specific)
```

- **Top**: Supertype of everything (knows nothing specific)
- **Bot**: Subtype of everything (has every capability... vacuously)

## Part 2: Record Subtyping

### Width Subtyping - More Fields

Here's the key insight that often trips up beginners:

**A record with MORE fields is a SUBTYPE of a record with FEWER fields.**

Why? Because having more fields means you can do everything the smaller record does, plus more!

```
{x: Nat, y: Bool, z: Top} <: {x: Nat, y: Bool} <: {x: Nat}
```

### Example: Points

```
-- A 2D point
type Point2D = {x: Nat, y: Nat}

-- A 3D point has everything Point2D has, plus z
type Point3D = {x: Nat, y: Nat, z: Nat}

-- Point3D <: Point2D
-- Any function expecting Point2D works with Point3D!

getX : Point2D -> Nat
getX = \p:{x: Nat, y: Nat}. p.x

-- This works:
getX {x = 1, y = 2, z = 3}
-- Because {x: Nat, y: Nat, z: Nat} <: {x: Nat, y: Nat}
```

### Depth Subtyping - More Specific Fields

If each field type is more specific, the whole record is more specific:

```
{x: Bot, y: Bot} <: {x: Nat, y: Bool}
-- Because Bot <: Nat and Bot <: Bool
```

### Combining Width and Depth

```
{x: Bot, y: Nat, extra: Bool} <: {x: Nat, y: Top}

-- Width: drop 'extra'
-- Depth: Bot <: Nat, Nat <: Top
```

## Part 3: Function Subtyping

This is where things get interesting!

### The Rule

```
  σ₁ <: τ₁    τ₂ <: σ₂
─────────────────────── (S-Arrow)
  τ₁ → τ₂ <: σ₁ → σ₂
```

Wait, the argument is *reversed*? Yes! This is called **contravariance**.

### Intuition: The Caller's Perspective

Think about what the *caller* provides:

```
-- If I have a function that handles ANY animal:
feedAnimal : Animal -> ()

-- Can I use it where a function handling dogs is expected?
registerDogHandler : (Dog -> ()) -> ()

-- YES! The caller will pass Dogs, and feedAnimal can handle Dogs
-- (because Dog <: Animal)

registerDogHandler feedAnimal  -- Works!
```

Now the reverse:

```
-- If I have a function for dogs only:
walkDog : Dog -> ()

-- Can I use it where an animal handler is expected?
registerAnimalHandler : (Animal -> ()) -> ()

-- NO! The caller might pass a Cat, and walkDog can't handle Cats!

registerAnimalHandler walkDog  -- Type error!
```

### The Covariant Part

Return types are **covariant** - they go the "normal" direction:

```
-- If a function returns a Dog:
getDog : () -> Dog

-- Can I use it where a function returning Animal is expected?
-- YES! Returning a Dog is fine when Animal is expected
-- (because Dog <: Animal)
```

### Putting It Together

```
(Top -> Bot) <: (Nat -> Bool)

-- Check argument: Nat <: Top? Yes!
-- Check result: Bot <: Bool? Yes!
-- Therefore the subtyping holds.
```

## Part 4: Type Checking with Subsumption

### The Subsumption Rule

```
  Γ ⊢ t : S    S <: T
─────────────────────── (T-Sub)
       Γ ⊢ t : T
```

This says: if a term has type S, it also has type T for any supertype T.

### Where It's Applied

In our implementation, subsumption is applied at:

1. **Function application**: Argument must be subtype of parameter
2. **Ascription**: Term type must be subtype of declared type
3. **If-then-else**: Branches are joined to find common supertype

### Example: Function Application

```
-- Define a function accepting Top
f : Top -> Nat
f = \x:Top. 0

-- Apply it to a Bool
f true

-- Type checking:
-- f : Top -> Nat
-- true : Bool
-- Need: Bool <: Top? YES!
-- Result: Nat
```

### Example: Record Subsumption

```
-- Function expecting {x: Nat}
getX : {x: Nat} -> Nat
getX = \r:{x: Nat}. r.x

-- Apply to {x: Nat, y: Bool}
getX {x = 5, y = true}

-- Type checking:
-- {x = 5, y = true} : {x: Nat, y: Bool}
-- Need: {x: Nat, y: Bool} <: {x: Nat}? YES (width subtyping)!
-- Result: Nat
```

## Part 5: Join and Meet

### Join: Least Upper Bound

The join of two types is the *smallest* type that's a supertype of both.

Used for: if-then-else branches

```
if condition then expr1 else expr2

-- expr1 : T1
-- expr2 : T2
-- result : T1 ⊔ T2 (join)
```

### Examples of Join

```
Nat ⊔ Nat = Nat          -- Same type
Nat ⊔ Bool = Top         -- No common supertype except Top
Bot ⊔ Nat = Nat          -- Bot is absorbed
Top ⊔ Nat = Top          -- Top absorbs

{x: Nat, y: Bool} ⊔ {x: Nat, z: Top} = {x: Nat}
-- Only common fields remain!
```

### Meet: Greatest Lower Bound

The meet is the *largest* type that's a subtype of both.

Used for: function arguments when computing join of functions.

```
{x: Nat} ⊓ {y: Bool} = {x: Nat, y: Bool}
-- All fields combined!
```

### Function Join/Meet

For functions, variance flips things:

```
(S1 -> R1) ⊔ (S2 -> R2) = (S1 ⊓ S2) -> (R1 ⊔ R2)
-- Meet the arguments (contravariant)
-- Join the results (covariant)
```

## Part 6: Practical Examples

### Object-Oriented Patterns

Subtyping models inheritance:

```
-- Base "class"
type Shape = {area: Nat}

-- Derived "class" (subtype)
type Circle = {area: Nat, radius: Nat}

-- Derived "class" (subtype)
type Rectangle = {area: Nat, width: Nat, height: Nat}

-- Function works on any shape
printArea : Shape -> Nat
printArea = \s:{area: Nat}. s.area

-- Works on Circle and Rectangle too!
printArea {area = 100, radius = 10}
printArea {area = 50, width = 5, height = 10}
```

### Upcasting with Ascription

Sometimes you want to explicitly forget information:

```
-- We have a colored point
coloredPoint : {x: Nat, y: Nat, color: Bool}
coloredPoint = {x = 0, y = 0, color = true}

-- Upcast to regular point
point : {x: Nat, y: Nat}
point = coloredPoint as {x: Nat, y: Nat}
```

### Handling Multiple Return Types

```
-- Function might return different record types
getShape : Bool -> {area: Nat}
getShape = \isCircle:Bool.
  if isCircle
    then ({area = 100, radius = 10} as {area: Nat})
    else ({area = 50, width = 5, height = 10} as {area: Nat})
```

## Part 7: Common Pitfalls

### Pitfall 1: Width Subtyping Direction

WRONG thinking: "Smaller record is subtype"
RIGHT thinking: "Record with MORE fields is subtype"

```
{x: Nat, y: Bool} <: {x: Nat}  -- YES
{x: Nat} <: {x: Nat, y: Bool}  -- NO!
```

### Pitfall 2: Function Argument Direction

WRONG: `(Dog -> R) <: (Animal -> R)` if `Dog <: Animal`
RIGHT: `(Animal -> R) <: (Dog -> R)` if `Dog <: Animal`

The argument subtyping is **reversed**!

### Pitfall 3: Forgetting Join Loses Fields

```
if true then {x = 0, y = true} else {x = 0, z = false}
-- Type: {x: Nat}, NOT {x: Nat, y: Bool, z: Bool}!
```

Only *common* fields survive the join.

## Practice Problems

### Problem 1
Does `{f: Top -> Bot} <: {f: Bool -> Nat}` hold?

<details>
<summary>Solution</summary>

Yes! Let's check:
- This is record depth subtyping, so check the field `f`
- Need: `Top -> Bot <: Bool -> Nat`?
- Check arg: `Bool <: Top`? Yes!
- Check result: `Bot <: Nat`? Yes!
- Therefore: Yes, the subtyping holds.

</details>

### Problem 2
What is `(Nat -> Bool) ⊔ (Bool -> Nat)`?

<details>
<summary>Solution</summary>

Using the join rule for functions:
```
(Nat -> Bool) ⊔ (Bool -> Nat)
= (Nat ⊓ Bool) -> (Bool ⊔ Nat)
= Bot -> Top
```

Since Nat and Bool have no common subtype except Bot, their meet is Bot.
Since Nat and Bool have no common supertype except Top, their join is Top.

</details>

### Problem 3
Can you pass `\x:Top. 0` where `Bool -> Nat` is expected?

<details>
<summary>Solution</summary>

Yes! We need `Top -> Nat <: Bool -> Nat`.
- Check arg: `Bool <: Top`? Yes!
- Check result: `Nat <: Nat`? Yes!

So `\x:Top. 0` can be used wherever `Bool -> Nat` is expected.

</details>
