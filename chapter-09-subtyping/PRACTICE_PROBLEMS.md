# Chapter 9: Subtyping - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce subtyping concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Basic Subtyping ⭐
Which of these subtyping relationships hold?

a) `Bool <: Top`
b) `Bot <: Nat`
c) `{x: Nat, y: Bool} <: {x: Nat}`
d) `{x: Nat} <: {x: Nat, y: Bool}`
e) `Top <: Bool`

### Problem 1.2: Function Subtyping ⭐
Which of these hold?

a) `(Top → Nat) <: (Bool → Nat)`
b) `(Bool → Nat) <: (Top → Nat)`
c) `(Nat → Bot) <: (Nat → Bool)`
d) `(Nat → Bool) <: (Nat → Bot)`

### Problem 1.3: Record Width ⭐
Determine if these are subtypes:

a) `{x: Nat, y: Nat, z: Bool} <: {x: Nat}`
b) `{name: Bool} <: {name: Bool, age: Nat}`
c) `{a: Nat, b: Nat, c: Nat} <: {a: Nat, b: Nat}`

### Problem 1.4: Computing Join ⭐
Compute these joins:

a) `Nat ⊔ Nat`
b) `Bool ⊔ Nat`
c) `Bot ⊔ Nat`
d) `Top ⊔ Bool`
e) `{x: Nat, y: Bool} ⊔ {x: Nat, z: Top}`

### Problem 1.5: Computing Meet ⭐
Compute these meets:

a) `Nat ⊓ Nat`
b) `Bool ⊓ Nat`
c) `Top ⊓ Nat`
d) `Bot ⊓ Bool`
e) `{x: Nat} ⊓ {y: Bool}`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Variance Analysis ⭐⭐
For each type, determine the variance of `X`:

a) `X → Bool`
b) `Bool → X`
c) `(X → Bool) → Nat`
d) `(Bool → X) → Nat`
e) `((X → Bool) → Nat) → Top`
f) `X → (Bool → X)`

### Problem 2.2: Complex Function Subtyping ⭐⭐
Does `(Top → Bot) → (Nat → Bool)` <: `(Nat → Bool) → (Bool → Nat)`?

Break down the check step by step.

### Problem 2.3: Record Depth Subtyping ⭐⭐
Which of these hold?

a) `{x: Bot, y: Nat} <: {x: Nat, y: Top}`
b) `{f: Top → Bot} <: {f: Bool → Nat}`
c) `{a: {x: Nat, y: Bool}} <: {a: {x: Nat}}`

### Problem 2.4: Join of Functions ⭐⭐
Compute:

a) `(Nat → Bool) ⊔ (Bool → Nat)`
b) `(Top → Nat) ⊔ (Bool → Top)`
c) `(Nat → Nat) ⊔ (Nat → Bool)`

### Problem 2.5: Meet of Records ⭐⭐
Compute:

a) `{x: Nat} ⊓ {y: Bool}`
b) `{x: Nat, y: Bool} ⊓ {x: Bool, z: Top}`
c) `{f: Nat → Bool} ⊓ {f: Bool → Nat}`

### Problem 2.6: Ascription Type Checking ⭐⭐
Which of these ascriptions type check?

a) `true as Top`
b) `0 as Bool`
c) `{x = 0, y = true} as {x: Nat}`
d) `(\x:Top. x) as (Nat → Nat)`
e) `(\x:Nat. 0) as (Top → Nat)`

### Problem 2.7: If-Then-Else Types ⭐⭐
What is the type of each expression?

a) `if true then 0 else 1`
b) `if true then true else false`
c) `if true then {x = 0} else {x = 1, y = true}`
d) `if true then (\x:Nat. x) else (\x:Bool. x)`
e) `if true then {f = \x:Top. 0} else {f = \x:Bool. 1}`

### Problem 2.8: Designing Subtype Relations ⭐⭐
Design a set of record types representing:
- `Vehicle` (has `wheels: Nat`)
- `Car` (has `wheels: Nat`, `doors: Nat`)
- `Truck` (has `wheels: Nat`, `doors: Nat`, `cargo: Nat`)

Show the subtyping relationships.

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Transitivity Proof ⭐⭐⭐
Prove that subtyping is transitive for function types:

If `(S₁ → S₂) <: (T₁ → T₂)` and `(T₁ → T₂) <: (U₁ → U₂)`, then `(S₁ → S₂) <: (U₁ → U₂)`.

### Problem 3.2: Join Lattice Properties ⭐⭐⭐
Prove that join is:

a) **Commutative**: `τ₁ ⊔ τ₂ = τ₂ ⊔ τ₁`
b) **Associative**: `τ₁ ⊔ (τ₂ ⊔ τ₃) = (τ₁ ⊔ τ₂) ⊔ τ₃`
c) **Idempotent**: `τ ⊔ τ = τ`

### Problem 3.3: Why No Downcast? ⭐⭐⭐
Explain why allowing downcasting (from supertype to subtype) would be unsafe:

```
-- If this were allowed:
x : Top
y : Nat = x as Nat    -- downcast

-- What could go wrong?
```

Give a concrete example of the unsoundness.

### Problem 3.4: Mutable Reference Invariance ⭐⭐⭐
Prove that mutable references must be invariant:

a) Show why `Ref[Dog] <: Ref[Animal]` is unsound (if `Dog <: Animal`)
b) Show why `Ref[Animal] <: Ref[Dog]` is unsound
c) Conclude that `Ref` must be invariant

### Problem 3.5: Intersection Types ⭐⭐⭐
Suppose we extend the system with intersection types `τ₁ ∧ τ₂` (has both τ₁ and τ₂'s capabilities).

a) Define subtyping rules for intersections
b) How does `∧` relate to meet (`⊓`)?
c) Give the type of: `\x:(Nat ∧ Bool). if (iszero x) then x else x`

### Problem 3.6: Union Types ⭐⭐⭐
Now add union types `τ₁ ∨ τ₂` (has either τ₁ or τ₂'s capabilities).

a) Define subtyping rules for unions
b) How does `∨` relate to join (`⊔`)?
c) Can you type check `\x:(Nat ∨ Bool). succ x`? Why or why not?

### Problem 3.7: Bounded Quantification ⭐⭐⭐
Extend to bounded quantification `∀α <: T. τ`:

a) Define the typing rule for type abstraction
b) Define the typing rule for type application
c) Give an example use case
d) Compare with System F (unbounded quantification)

### Problem 3.8: Algorithmic Subtyping Termination ⭐⭐⭐
Prove that the algorithmic subtyping judgment terminates:

```haskell
subtype :: Type -> Type -> Bool
```

Hint: Use structural induction on types. What is the decreasing metric?

---

## Debugging Exercises (30 minutes)

### Debug 1: Width Direction ⭐
What's wrong with this claim?

```
{x: Nat} <: {x: Nat, y: Bool, z: Top}
```

Fix it.

### Debug 2: Contravariance Confusion ⭐
Student claims:

```
(Dog → String) <: (Animal → String)  -- Given: Dog <: Animal
```

What's the error? Explain why it's backwards.

### Debug 3: Join Confusion ⭐⭐
Student wrote:

```
if true then {x = 0, y = true} else {x = 1, z = false}
-- Type: {x: Nat, y: Bool, z: Bool}
```

What's wrong? What's the actual type?

### Debug 4: Function Join ⭐⭐
Student computed:

```
(Nat → Bool) ⊔ (Bool → Nat) = Top
```

Is this correct? If not, what's the right answer?

### Debug 5: Ascription Downcast ⭐⭐
Why doesn't this work?

```
x : Top = true as Top
y : Bool = x as Bool    -- Type error!
```

Explain the error and how to fix the code.

### Debug 6: Depth and Width ⭐⭐
Does this subtyping hold?

```
{x: Bot, y: Nat, extra: Bool} <: {x: Nat, y: Top}
```

Work through it step by step.

---

## Code Review Exercises (30 minutes)

### Review 1: Type-Safe Upcasting ⭐⭐
Review this code:

```haskell
point2D : {x: Nat, y: Nat}
point2D = {x = 0, y = 0}

point3D : {x: Nat, y: Nat, z: Nat}
point3D = {x = 1, y = 2, z = 3}

getX : {x: Nat} -> Nat
getX = \p:{x: Nat}. p.x

-- Usage:
getX point2D
getX point3D
getX {x = 5, y = 10, z = 15, color = true}
```

Verify the subtyping relationships. Are all usages valid?

### Review 2: Function Subsumption ⭐⭐
Two implementations of a higher-order function:

**Version A**:
```
apply : (Bool -> Nat) -> Bool -> Nat
apply = \f:(Bool -> Nat). \x:Bool. f x
```

**Version B**:
```
apply : (Top -> Nat) -> Bool -> Nat
apply = \f:(Top -> Nat). \x:Bool. f x
```

Which is more general? Can you pass a `Top -> Nat` to version A?

### Review 3: Join Optimization ⭐⭐⭐
Student code:

```haskell
classify : Nat -> {type: Bool}
classify = \n:Nat.
  if (iszero n)
    then ({type = true, zero = true} as {type: Bool})
    else ({type = false, positive = true} as {type: Bool})
```

Questions:
- Why are the ascriptions needed?
- Is there a better design?
- What are the tradeoffs?

### Review 4: Variance in Data Structures ⭐⭐⭐
Design a `List` type with subtyping:

```haskell
-- Option 1: Covariant
List[Dog] <: List[Animal]

-- Option 2: Invariant
No subtyping between List[Dog] and List[Animal]
```

Discuss:
- Which is better for immutable lists?
- What if lists are mutable?
- How does this relate to Java/Scala?

---

## Real-World Applications (30 minutes)

### Application 1: Object-Oriented Design ⭐⭐
Model an OOP class hierarchy:

```
class Animal { eat(): void }
class Dog extends Animal { bark(): void }
class Cat extends Animal { meow(): void }
```

Using records:
- Define the types
- Show subtyping relationships
- Write a function that works on any Animal

### Application 2: API Versioning ⭐⭐
You have an API:

```
v1 : {name: String}
v2 : {name: String, email: String}
v3 : {name: String, email: String, phone: String}
```

Questions:
- What are the subtyping relationships?
- Can v3 clients call v1 APIs?
- Can v1 clients call v3 APIs?

### Application 3: TypeScript Compatibility ⭐⭐⭐
TypeScript has structural subtyping. Given:

```typescript
interface Point { x: number; y: number }
interface NamedPoint { x: number; y: number; name: string }

function distance(p: Point): number {
  return Math.sqrt(p.x * p.x + p.y * p.y);
}

distance({ x: 3, y: 4, name: "origin" });
```

Explain:
- Why does this work?
- How does it relate to our width subtyping?
- What are potential pitfalls?

---

## Solutions

### Warm-Up Solutions

**1.1**: a) Yes, b) Yes, c) Yes, d) No, e) No

**1.2**: a) Yes (contravariant arg: Bool <: Top), b) No, c) Yes (Bot <: Bool), d) No

**1.3**: a) Yes (width), b) No (backwards), c) Yes (width)

**1.4**:
- a) `Nat`
- b) `Top`
- c) `Nat`
- d) `Top`
- e) `{x: Nat}` (only common field)

**1.5**:
- a) `Nat`
- b) `Bot`
- c) `Nat`
- d) `Bot`
- e) `{x: Nat, y: Bool}` (all fields)

### Standard Solutions

**2.1**:
- a) Contravariant (-)
- b) Covariant (+)
- c) Covariant (+ from - × -)
- d) Contravariant (- from + × -)
- e) Contravariant (- from + × (- × -) × -)
- f) Contravariant (- from + × (+ × -))

**2.2**:
Check: `(Top → Bot) → (Nat → Bool) <: (Nat → Bool) → (Bool → Nat)`
- Argument: Need `(Nat → Bool) <: (Top → Bot)`
  - Arg: Need `Top <: Nat`? NO! Fails here.
- Answer: No

**2.3**: a) Yes (depth), b) Yes (depth + function subtyping), c) Yes (depth)

**2.4**:
- a) `Bot → Top` (meet args, join results)
- b) `(Top ⊓ Bool) → (Nat ⊔ Top) = Bool → Top`
- c) `Nat → (Nat ⊔ Bool) = Nat → Top`

**2.5**:
- a) `{x: Nat, y: Bool}`
- b) `{x: (Nat ⊓ Bool), y: Bool, z: Top} = {x: Bot, y: Bool, z: Top}`
- c) `{f: (Nat ⊔ Bool) → (Bool ⊓ Nat)} = {f: Top → Bot}`

**2.6**: a) Yes, b) No, c) Yes, d) No (need Top <: Nat), e) Yes

**2.7**:
- a) `Nat`
- b) `Bool`
- c) `{x: Nat}`
- d) `Top → Top` or error (no good join of Nat and Bool)
- e) `{f: Bool → Nat}` (join the function types)

**2.8**:
```
Vehicle = {wheels: Nat}
Car = {wheels: Nat, doors: Nat}
Truck = {wheels: Nat, doors: Nat, cargo: Nat}

Truck <: Car <: Vehicle
```

### Challenge Solutions

**3.1**: Use transitivity of contravariant arguments and covariant results.

**3.2**: These follow from properties of least upper bounds in a lattice.

**3.3**:
```
x : Top = true
y : Nat = x as Nat    -- If allowed, y would be true : Nat
succ y                -- Type checks but runtime error!
```

**3.4**: Covariance allows write violations, contravariance allows read violations.

**3.5**:
- a) `τ₁ ∧ τ₂ <: τ₁` and `τ₁ ∧ τ₂ <: τ₂`
- b) Intersection IS meet for types
- c) Type error: can't iszero a Bool

**3.6**:
- a) `τ₁ <: τ₁ ∨ τ₂` and `τ₂ <: τ₁ ∨ τ₂`
- b) Union IS join
- c) No: union doesn't guarantee Nat

**3.7**: Similar to System F but with subtype bounds

**3.8**: Structural recursion on sum of type sizes always decreases

### Debug Solutions

**Debug 1**: Wrong direction. Should be `{x: Nat, y: Bool, z: Top} <: {x: Nat}`

**Debug 2**: Arguments are contravariant: `(Animal → String) <: (Dog → String)`

**Debug 3**: Join keeps only common fields: `{x: Nat}`

**Debug 4**: Correct! `(Nat ⊓ Bool) → (Bool ⊔ Nat) = Bot → Top`

**Debug 5**: Can't downcast. Need to maintain x : Top or restructure code.

**Debug 6**: Yes! Width: drop `extra`. Depth: `Bot <: Nat`, `Nat <: Top`.

---

**Estimated Time**: 3-5 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 8 hard, 6 debug, 4 review

**Note**: These problems complement the main exercises. Focus on understanding variance and subtyping direction!
