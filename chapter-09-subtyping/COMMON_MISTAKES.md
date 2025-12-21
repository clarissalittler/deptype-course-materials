# Chapter 9: Subtyping - Common Mistakes

This guide covers the most frequent errors when learning subtyping, how to recognize them, and how to fix them.

---

## Mistake 1: Width Subtyping Direction

### The Problem
Thinking that records with *fewer* fields are subtypes.

### Wrong Thinking
> "A smaller record is more specific, so it should be a subtype."

```
{x: Nat} <: {x: Nat, y: Bool}  -- WRONG!
```

### Correct Understanding
Records with **more** fields are subtypes because they have all the capabilities of the smaller record, plus more.

```
{x: Nat, y: Bool} <: {x: Nat}  -- CORRECT!
```

### Why This Makes Sense
If a function expects `{x: Nat}`, it only uses the `x` field. A record with `{x: Nat, y: Bool}` can provide that `x` field. The extra `y` is just ignored.

### How to Remember
> "A record with more fields can do everything a record with fewer fields can do."

---

## Mistake 2: Function Argument Direction

### The Problem
Thinking that function argument subtyping goes the same direction as everything else.

### Wrong Thinking
> "If Dog <: Animal, then (Dog -> R) <: (Animal -> R)."

```
(Dog -> String) <: (Animal -> String)  -- WRONG!
```

### Correct Understanding
Function arguments are **contravariant** - the direction is reversed:

```
(Animal -> String) <: (Dog -> String)  -- CORRECT!
```

### Why This Makes Sense
Think about what the *caller* provides:
- If code expects `Dog -> String`, callers will pass Dogs
- A function `Animal -> String` can handle Dogs (Dogs are Animals)
- But a function `Dog -> String` can't handle all Animals (what about Cats?)

### How to Remember
> "The function receives the argument. If it can handle more general inputs, it's more flexible."

---

## Mistake 3: Confusing Top and Bot Roles

### The Problem
Mixing up which is supertype of everything vs. subtype of everything.

### Wrong Thinking
> "Bot is at the bottom, so everything is below it (subtype)."

### Correct Understanding
- **Top**: Supertype of everything. `τ <: Top` for all τ.
- **Bot**: Subtype of everything. `Bot <: τ` for all τ.

### Visual Aid
```
        Top (everything goes UP to here)
       / | \
     ... ... ...
       \ | /
        Bot (everything comes DOWN from here)
```

### How to Remember
> "Everything CAN BE a Top. Bot CAN BE anything."

---

## Mistake 4: Expecting Ascription to Downcast

### The Problem
Trying to use ascription to cast to a more specific type.

### Wrong Code
```
(someValue as {x: Nat})  -- where someValue : Top
-- ERROR: Top is not a subtype of {x: Nat}
```

### Correct Understanding
Ascription only allows **upcasting** (to a supertype):

```
{x = 0, y = true} as {x: Nat}  -- OK: {x: Nat, y: Bool} <: {x: Nat}
true as Top                     -- OK: Bool <: Top
```

### Why This Is Important
Downcasting would be unsafe - you can't guarantee the value actually has the more specific type.

### How to Fix
If you need a more specific type, you need to either:
1. Have the value be that type from the start
2. Use runtime type checking (not available in this system)

---

## Mistake 5: Forgetting Join Loses Information

### The Problem
Expecting if-then-else to preserve all fields from both branches.

### Wrong Expectation
```
if true then {x = 0, y = true} else {x = 0, z = false}
-- Expected: {x: Nat, y: Bool, z: Bool}
-- Actual: {x: Nat}
```

### Correct Understanding
Join computes the *least upper bound* - only **common** fields are kept:

```
{x: Nat, y: Bool} ⊔ {x: Nat, z: Bool} = {x: Nat}
```

### Why This Happens
After the if-then-else, we don't know which branch executed. We can only rely on fields that exist in *both* possibilities.

### How to Fix
If you need all fields, restructure your code to ensure both branches have the same type, or use a discriminated union.

---

## Mistake 6: Missing Field in Record Subtype

### The Problem
Thinking subtyping works when the subtype is missing a required field.

### Wrong Thinking
```
{x: Nat} <: {x: Nat, y: Bool}  -- WRONG!
```

### Correct Understanding
The alleged subtype must have **all fields** of the supertype. Having fewer fields means it *can't* do everything the supertype can.

### Debugging Tip
When record subtyping fails, check:
1. Does the subtype have every field in the supertype?
2. Is each field's type a subtype of the corresponding supertype field?

---

## Mistake 7: Variance in Nested Functions

### The Problem
Getting confused about variance when functions are nested.

### Tricky Example
```
In type ((A -> B) -> C):
- What's the variance of A?
- What's the variance of B?
```

### Correct Understanding
Variance multiplies:
- Covariant (+) × Covariant (+) = Covariant (+)
- Covariant (+) × Contravariant (-) = Contravariant (-)
- Contravariant (-) × Contravariant (-) = Covariant (+)

For `((A -> B) -> C)`:
- C is covariant (+)
- `(A -> B)` is in argument position, so contravariant (-)
- A is in argument of that, so (- × -) = + (covariant!)
- B is in result of that, so (+ × -) = - (contravariant)

### How to Remember
> "Each arrow to the left of a position flips the variance."

---

## Mistake 8: Mutable References Should Be Covariant

### The Problem
Thinking mutable references should follow normal subtyping rules.

### Wrong Thinking
> "If Dog <: Animal, then Ref[Dog] <: Ref[Animal]."

### Correct Understanding
Mutable references are **invariant** - neither covariant nor contravariant.

### Why Covariance Breaks
```
ref : Ref[Dog]
refAsAnimal : Ref[Animal] = ref  -- If this were allowed...
write(refAsAnimal, new Cat())    -- Write a Cat!
dog : Dog = read(ref)            -- Read it as Dog - CRASH!
```

### Why Contravariance Also Breaks
```
ref : Ref[Animal]
refAsDog : Ref[Dog] = ref        -- If this were allowed...
dog : Dog = read(refAsDog)       -- Read it as Dog...
-- But ref might contain a Cat! CRASH!
```

### Takeaway
Anything that's both read and written must be invariant.

---

## Mistake 9: Subtyping vs. Type Equality

### The Problem
Confusing `S <: T` with `S = T`.

### Wrong Code
```
-- If we have f : {x: Nat} -> Nat
-- Can we pass it where g : {x: Nat, y: Bool} -> Nat is expected?
```

### Correct Understanding
- `S <: T` means S can be *used as* T, not that they're equal
- For the example: We need `{x: Nat} -> Nat <: {x: Nat, y: Bool} -> Nat`
- That requires `{x: Nat, y: Bool} <: {x: Nat}` (contravariance!)
- This is TRUE, so yes, it works.

### Key Insight
Subtyping is about substitutability, not equality. Many different types can all be subtypes of the same type.

---

## Mistake 10: Forgetting Bot is Uninhabited

### The Problem
Trying to create values of type Bot.

### Wrong Thinking
> "Bot is a type, so there must be values of that type."

### Correct Understanding
In a sound type system, there are **no values of type Bot**. Bot represents:
- Computations that never return (infinite loops)
- Functions that always throw exceptions
- Impossible cases

### Why This Matters
- `Bot -> T` is a valid function type, but you can never call such a function (no Bot values to pass)
- If you have a value of type Bot, you've found a bug or unsoundness

---

## Debugging Checklist

When subtyping isn't working as expected:

1. **Check the direction**: Is S supposed to be the subtype?
2. **For records**: Does S have all fields of T? Are field types subtypes?
3. **For functions**: Remember contravariance! Is the argument check reversed?
4. **For nested types**: Trace through variance carefully
5. **For ascription**: Are you trying to downcast? That's not allowed.
6. **For conditionals**: Join only keeps common fields

---

## Practice Problems

### Problem 1: Fix the Subtyping
What's wrong with this claim?

```
{a: Nat} <: {a: Nat, b: Bool}
```

<details>
<summary>Answer</summary>

The direction is backwards. Records with more fields are subtypes:
```
{a: Nat, b: Bool} <: {a: Nat}  -- CORRECT
```

</details>

### Problem 2: Fix the Function Subtyping
What's wrong here?

```
(Dog -> String) <: (Animal -> String)  -- Given: Dog <: Animal
```

<details>
<summary>Answer</summary>

Function arguments are contravariant. The correct relationship is:
```
(Animal -> String) <: (Dog -> String)
```

A function that handles Animals can be used where a Dog handler is needed.

</details>

### Problem 3: Why Doesn't This Type Check?

```
(\x:Nat. x) as (Top -> Nat)
```

<details>
<summary>Answer</summary>

We need `Nat -> Nat <: Top -> Nat`.
- Argument: Need `Top <: Nat`? NO! Top is not a subtype of Nat.

The function `\x:Nat. x` expects Nat, but `Top -> Nat` promises to accept anything. That's not safe.

</details>

### Problem 4: What's the Result Type?

```
if true then {x = 0, y = true, z = false} else {x = 0}
```

<details>
<summary>Answer</summary>

The result type is `{x: Nat}` because:
- Branch 1: `{x: Nat, y: Bool, z: Bool}`
- Branch 2: `{x: Nat}`
- Join: Only `x` is common, so `{x: Nat}`

</details>
