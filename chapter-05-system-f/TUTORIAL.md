# Chapter 5: System F (Polymorphic Lambda Calculus) - Tutorial

## Introduction

Welcome to the System F tutorial! This document walks you through explicit polymorphism with detailed, step-by-step examples. System F might feel verbose at first (all those type annotations!), but it's incredibly powerful - you can finally pass polymorphic functions as arguments and return them from functions.

Think of this as sitting down with a tutor who shows you not just what to do, but why each step works and what it means.

**What makes System F special?**
- Polymorphism is **explicit** and **first-class**
- You can abstract over types just like you abstract over values
- You can apply types just like you apply terms
- The type system is fully expressive (but type inference is impossible)

---

## Part 1: Type Abstraction and Application - The New Constructs

### From Values to Types

You're already familiar with abstracting over values:
```
λx:Nat. x + 1    (function taking a Nat)
```

System F adds abstraction over **types**:
```
Λα. λx:α. x      (function taking a TYPE α, then a value of type α)
```

Think of `Λα` as saying "give me a type called α, and I'll give you a function."

### Breaking Down Polymorphic Identity

Let's examine the polymorphic identity function step by step:

```
id = Λα. λx:α. x
```

**Reading it piece by piece:**
- `Λα` - "abstract over a type variable α"
- `.` - "in the following term..."
- `λx:α` - "take a value x of type α"
- `.` - "and return..."
- `x` - "that value unchanged"

**The type:**
```
id : ∀α. α → α
```

**Reading the type:**
- `∀α` - "for all types α"
- `.` - "this has type..."
- `α → α` - "function from α to α"

### Using Polymorphic Identity

To use `id`, you must **apply it to a type first**:

```
id [Bool]        : Bool → Bool
id [Nat]         : Nat → Nat
id [∀β. β → β]   : (∀β. β → β) → (∀β. β → β)
```

Then you can apply it to a value:

```
id [Bool] true   →  true
id [Nat] 42      →  42
```

**Step-by-step evaluation:**
```
  id [Bool] true
= (Λα. λx:α. x) [Bool] true    (expand id)
→ (λx:Bool. x) true             (type β-reduction: substitute Bool for α)
→ true                          (term β-reduction)
```

### Why Can't We Omit Type Applications?

You might wonder: "Can't the system figure out I mean `Bool` from context?"

**Answer**: In general, no! Type inference for System F is **undecidable** (proven by Wells in 1999).

Some type applications can be inferred locally (called "local type inference"), but System F requires explicit type applications to be decidable.

---

## Part 2: Universal Types (∀α. τ)

### What Does ∀ Mean?

The `∀` (universal quantifier) means "for all types."

**Example types:**
```
∀α. α → α                          (identity on any type)
∀α. ∀β. α → β → α                  (const: returns first arg)
∀α. ∀β. (α → β) → α → β            (apply function)
∀α. ∀β. ∀γ. (β→γ) → (α→β) → α→γ   (compose functions)
```

### Scope of Type Variables

Type variables are scoped by their ∀:

```
∀α. α → (∀β. β → α)
```

Here:
- `α` is bound by the outer `∀α`
- `β` is bound by the inner `∀β`
- The final `α` refers to the outer one

**As a function:**
```
Λα. λx:α. Λβ. λy:β. x
```

This takes a type α, a value x:α, then another type β, a value y:β, and returns x (ignoring y).

### Multiple Type Parameters

When you see multiple ∀s, they can be written in sequence:

```
∀α. ∀β. ∀γ. τ    is the same as    ∀α β γ. τ   (shorthand)
```

**Example: Composition**
```
compose : ∀α. ∀β. ∀γ. (β → γ) → (α → β) → (α → γ)

compose = Λα. Λβ. Λγ. λf:β→γ. λg:α→β. λx:α. f (g x)
```

**Using it:**
```
compose [Nat] [Bool] [String] show not 42
```

This applies `not` then `show`:
1. Type applications: instantiate α=Nat, β=Bool, γ=String
2. Term applications: pass `show:Bool→String`, `not:Nat→Bool`, `42:Nat`

---

## Part 3: Typing Rules for Polymorphism

### Two Contexts: Δ and Γ

System F uses **two contexts**:

- **Δ** (Delta): tracks which type variables are in scope
- **Γ** (Gamma): tracks which term variables (and their types) are in scope

**Example:**
```
Δ = {α, β}
Γ = {x:α, f:α→β}
```

This means:
- Type variables α and β are in scope
- Term variable x has type α
- Term variable f has type α→β

### Rule: T-TyAbs (Type Abstraction)

**Formal rule:**
```
Δ, α; Γ ⊢ t : τ
────────────────────  (T-TyAbs)
Δ; Γ ⊢ Λα. t : ∀α. τ
```

**Reading it:**
- Above the line: "If t has type τ when α is in scope..."
- Below the line: "...then Λα. t has type ∀α. τ"

**Example: Polymorphic identity**
```
Goal: ⊢ Λα. λx:α. x : ∀α. α → α

Step 1: Show  α; x:α ⊢ λx:α. x : α → α
  Step 1a: Show  α; x:α ⊢ x : α
    ────────────────────  (T-Var)
    α; x:α ⊢ x : α

  ──────────────────────────  (T-Abs)
  α; ⊢ λx:α. x : α → α

Step 2: Apply T-TyAbs
  ──────────────────────────────────  (T-TyAbs)
  ⊢ Λα. λx:α. x : ∀α. α → α
```

### Rule: T-TyApp (Type Application)

**Formal rule:**
```
Δ; Γ ⊢ t : ∀α. τ    Δ; Γ ⊢ τ' type
─────────────────────────────────  (T-TyApp)
Δ; Γ ⊢ t [τ'] : [α ↦ τ']τ
```

**Reading it:**
- If t has type ∀α. τ (a polymorphic type)
- And τ' is a valid type
- Then t[τ'] has type τ with α replaced by τ'

**Example: Using polymorphic identity**
```
Goal: ⊢ (Λα. λx:α. x) [Bool] : Bool → Bool

Step 1: Show ⊢ Λα. λx:α. x : ∀α. α → α  (we did this above)
Step 2: Show ⊢ Bool type                 (Bool is a valid type)
Step 3: Apply T-TyApp
  Type substitution: [α ↦ Bool](α → α) = Bool → Bool

  ────────────────────────────────────────────  (T-TyApp)
  ⊢ (Λα. λx:α. x) [Bool] : Bool → Bool
```

---

## Part 4: Complete Type Derivations

### Example 1: Polymorphic Const

Let's type check: `Λα. Λβ. λx:α. λy:β. x`

**Expected type:** `∀α. ∀β. α → β → α`

**Full derivation:**
```
Goal: ⊢ Λα. Λβ. λx:α. λy:β. x : ∀α. ∀β. α → β → α

  Goal: α; ⊢ Λβ. λx:α. λy:β. x : ∀β. α → β → α

    Goal: α, β; ⊢ λx:α. λy:β. x : α → β → α

      Goal: α, β; x:α ⊢ λy:β. x : β → α

        Goal: α, β; x:α, y:β ⊢ x : α

        ────────────────────────────  (T-Var, x:α ∈ Γ)
        α, β; x:α, y:β ⊢ x : α

      ──────────────────────────────  (T-Abs)
      α, β; x:α ⊢ λy:β. x : β → α

    ────────────────────────────────────  (T-Abs)
    α, β; ⊢ λx:α. λy:β. x : α → β → α

  ────────────────────────────────────────────  (T-TyAbs)
  α; ⊢ Λβ. λx:α. λy:β. x : ∀β. α → β → α

──────────────────────────────────────────────────  (T-TyAbs)
⊢ Λα. Λβ. λx:α. λy:β. x : ∀α. ∀β. α → β → α
```

### Example 2: Self-Application

One amazing thing about System F: polymorphic identity can be applied to itself!

```
polyId = Λα. λx:α. x : ∀α. α → α

polyId [∀β. β → β] polyId : ∀β. β → β
```

**Why does this work?**

1. `polyId : ∀α. α → α`
2. Instantiate α with `∀β. β → β`:
   ```
   polyId [∀β. β → β] : (∀β. β → β) → (∀β. β → β)
   ```
3. Apply to `polyId : ∀β. β → β`:
   ```
   polyId [∀β. β → β] polyId : ∀β. β → β
   ```

This is **impredicative instantiation** - we instantiated a type variable with a polymorphic type!

---

## Part 5: Evaluation - Type β-Reduction

### Type Reduction Rule

Just like term β-reduction:
```
(λx:τ. t) v  →  [x ↦ v]t     (term β-reduction)
```

System F has type β-reduction:
```
(Λα. t) [τ]  →  [α ↦ τ]t     (type β-reduction)
```

**Reading:** Applying a type abstraction to a type τ substitutes τ for α in the body.

### Example: Identity at Bool

```
(Λα. λx:α. x) [Bool] true

Step 1: Type application
  (Λα. λx:α. x) [Bool]
→ [α ↦ Bool](λx:α. x)        (type β-reduction)
= λx:Bool. x                 (substitute Bool for α)

Step 2: Term application
  (λx:Bool. x) true
→ [x ↦ true]x                (term β-reduction)
= true
```

### Example: Multiple Type Applications

```
(Λα. Λβ. λx:α. λy:β. x) [Nat] [Bool] 5 true

Step 1: First type application
  (Λα. Λβ. λx:α. λy:β. x) [Nat]
→ Λβ. λx:Nat. λy:β. x        (substitute Nat for α)

Step 2: Second type application
  (Λβ. λx:Nat. λy:β. x) [Bool]
→ λx:Nat. λy:Bool. x         (substitute Bool for β)

Step 3: First term application
  (λx:Nat. λy:Bool. x) 5
→ λy:Bool. 5                 (substitute 5 for x)

Step 4: Second term application
  (λy:Bool. 5) true
→ 5                          (substitute true for y, but y not used)
```

### Values in System F

A term is a **value** if it cannot reduce further:
```
v ::=
    λx:τ. t          (lambda abstraction)
    Λα. t            (type abstraction)
    true | false     (booleans)
    0 | succ v       (numbers)
```

Note: Type abstractions `Λα. t` are values - they don't reduce until applied to a type!

---

## Part 6: Church Encodings with Universal Types

### Why Universal Types Enable Encodings

In STLC (Chapter 2), we couldn't encode data types - we needed primitive types.

In System F, **universal types let us encode any data type!**

The key insight: A data type is defined by what you can do with it (its elimination form).

### Church Booleans in System F

**Type:**
```
CBool = ∀A. A → A → A
```

**Reading:** "For any type A, give me two values of type A (one for true case, one for false case), and I'll pick one."

**Encoding:**
```
true  = Λα. λt:α. λf:α. t   : ∀α. α → α → α
false = Λα. λt:α. λf:α. f   : ∀α. α → α → α
```

**Using a boolean:**
```
if b then x else y  ≡  b [typeof(x)] x y
```

**Example:**
```
if true then 5 else 10
= true [Nat] 5 10
= (Λα. λt:α. λf:α. t) [Nat] 5 10
→ (λt:Nat. λf:Nat. t) 5 10
→ (λf:Nat. 5) 10
→ 5
```

### Boolean Operations

**NOT:**
```
not : CBool → CBool
not = λb:CBool. Λα. λt:α. λf:α. b [α] f t
```

**How it works:** Swap the true and false cases!

**AND:**
```
and : CBool → CBool → CBool
and = λb1:CBool. λb2:CBool. Λα. λt:α. λf:α. b1 [α] (b2 [α] t f) f
```

**How it works:** If b1 is true, return b2's result; otherwise return false.

**Trace through `and true false`:**
```
  and true false [Nat] 1 0
= true [Nat] (false [Nat] 1 0) 0    (b1=true selects first arg)
= (Λα. λt:α. λf:α. t) [Nat] (false [Nat] 1 0) 0
→ (λt:Nat. λf:Nat. t) (false [Nat] 1 0) 0
→ (λf:Nat. (false [Nat] 1 0)) 0
→ false [Nat] 1 0
= (Λα. λt:α. λf:α. f) [Nat] 1 0
→ (λt:Nat. λf:Nat. f) 1 0
→ (λf:Nat. f) 0
→ 0
```

---

## Part 7: Church Numerals with ∀

### The Type

```
CNat = ∀α. (α → α) → α → α
```

**Reading:** "For any type α, give me a function f:α→α and a base value x:α, and I'll apply f some number of times to x."

### Encoding Numbers

```
zero = Λα. λf:α→α. λx:α. x                       (apply f 0 times)
one  = Λα. λf:α→α. λx:α. f x                     (apply f 1 time)
two  = Λα. λf:α→α. λx:α. f (f x)                 (apply f 2 times)
three = Λα. λf:α→α. λx:α. f (f (f x))            (apply f 3 times)
```

**Pattern:** n = apply f exactly n times

### Successor

```
succ : CNat → CNat
succ = λn:CNat. Λα. λf:α→α. λx:α. f (n [α] f x)
```

**How it works:** Apply f one more time after applying it n times!

**Trace `succ two`:**
```
succ two
= λn:CNat. Λα. λf:α→α. λx:α. f (n [α] f x)  (two)
= Λα. λf:α→α. λx:α. f (two [α] f x)

Now evaluate for concrete α, say Nat with f = (+1) and x = 0:
  f (two [Nat] f x)
= f (two [Nat] (+1) 0)
= f ((Λα. λf:α→α. λx:α. f (f x)) [Nat] (+1) 0)
→ f ((λf:Nat→Nat. λx:Nat. f (f x)) (+1) 0)
→ f ((λx:Nat. (+1) ((+1) x)) 0)
→ f ((+1) ((+1) 0))
= f ((+1) 1)
= f 2
= 3
```

### Addition

```
plus : CNat → CNat → CNat
plus = λm:CNat. λn:CNat. Λα. λf:α→α. λx:α. m [α] f (n [α] f x)
```

**Intuition:** Apply f n times, then apply f m more times = m+n total applications!

### Multiplication

```
mult : CNat → CNat → CNat
mult = λm:CNat. λn:CNat. Λα. λf:α→α. m [α] (n [α] f)
```

**Intuition:** Instead of applying f, apply (n [α] f), which applies f n times. Do this m times = m×n total applications!

---

## Part 8: Pairs and Lists

### Pair Encoding

```
Pair α β = ∀γ. (α → β → γ) → γ
```

**Reading:** "Give me a function that takes α and β and returns γ, and I'll call it with my two values."

**Constructor:**
```
pair : ∀α. ∀β. α → β → Pair α β
pair = Λα. Λβ. λa:α. λb:β. Λγ. λf:α→β→γ. f a b
```

**Projections:**
```
fst : ∀α. ∀β. Pair α β → α
fst = Λα. Λβ. λp:Pair α β. p [α] (λa:α. λb:β. a)

snd : ∀α. ∀β. Pair α β → β
snd = Λα. Λβ. λp:Pair α β. p [β] (λa:α. λb:β. b)
```

**Example:**
```
fst [Nat] [Bool] (pair [Nat] [Bool] 5 true)
= fst [Nat] [Bool] (Λγ. λf:Nat→Bool→γ. f 5 true)
= (Λγ. λf:Nat→Bool→γ. f 5 true) [Nat] (λa:Nat. λb:Bool. a)
→ (λf:Nat→Bool→Nat. f 5 true) (λa:Nat. λb:Bool. a)
→ (λa:Nat. λb:Bool. a) 5 true
→ (λb:Bool. 5) true
→ 5
```

### List Encoding

```
List α = ∀R. (α → R → R) → R → R
```

**Reading:** "Give me a function for cons and a value for nil, and I'll fold over my elements."

This is the **fold** function as a type!

**Constructors:**
```
nil : ∀α. List α
nil = Λα. ΛR. λc:α→R→R. λn:R. n

cons : ∀α. α → List α → List α
cons = Λα. λh:α. λt:List α. ΛR. λc:α→R→R. λn:R. c h (t [R] c n)
```

**Map:**
```
map : ∀α. ∀β. (α → β) → List α → List β
map = Λα. Λβ. λf:α→β. λlist:List α.
  list [List β]
    (λa:α. λrest:List β. cons [β] (f a) rest)
    (nil [β])
```

**How it works:**
- We fold over the input list
- For each element `a:α`, we apply `f:α→β` to get `f a : β`
- We cons it onto the accumulated result (which is a `List β`)
- We start with `nil [β]`

---

## Part 9: Parametricity and Free Theorems

### What is Parametricity?

**Parametricity Theorem (Reynolds):** A polymorphic function cannot inspect or create values of its type parameters - it can only manipulate them abstractly.

**Why?** Because the function doesn't know what the type is! It must work for ALL types.

### Example: Identity Must Be Identity

Consider a function:
```
f : ∀α. α → α
```

**Question:** What can f do?

**Answer:** It MUST return its input unchanged!

**Proof:**
- f cannot create a new value of type α (it doesn't know what α is)
- f cannot inspect the value (α might not support any operations)
- f can only return what it was given

Therefore: `f = Λα. λx:α. x` (the only possibility!)

### Free Theorem for List Functions

Consider:
```
f : ∀α. List α → List α
```

**What can f do?**
- Rearrange elements (reverse, sort, etc.)
- Duplicate elements
- Drop elements
- Return empty list

**What CAN'T f do?**
- Inspect element values (doesn't know what α is!)
- Modify elements
- Create new elements
- Compare elements

**Example valid functions:**
```
reverse : ∀α. List α → List α
take : ∀α. Nat → List α → List α
drop : ∀α. Nat → List α → List α
```

**Example INVALID functions:**
```
-- Can't filter by value - would need to inspect!
filterOdds : ∀α. List α → List α   ❌

-- CAN filter by position:
filterEveryOther : ∀α. List α → List α   ✓
```

### Free Theorem for Map

Consider:
```
map : ∀α. ∀β. (α → β) → List α → List β
```

**Free theorem:**
```
map g ∘ map f = map (g ∘ f)
```

**This is true for ANY implementation!** It follows from the type alone!

**Intuition:** Since map can't inspect elements, it must apply the function to each element. The order doesn't matter:
- Apply f to each, then apply g to each = apply (g ∘ f) to each

### Practical Impact

Parametricity gives us:
1. **Equational reasoning** - we can reason about code from types alone
2. **Free optimizations** - compiler can fuse operations safely
3. **Documentation** - types tell us what functions can/cannot do
4. **Bug prevention** - impossible to write certain incorrect implementations

---

## Part 10: Existential Types

### Encoding Existentials

System F doesn't have primitive existential types, but we can **encode** them using ∀:

```
∃α. τ  ≡  ∀R. (∀α. τ → R) → R
```

**Reading:** "To get a result of type R, you must provide a function that works for ANY type α."

### Pack and Unpack

**Pack:** Hide a type
```
pack : ∀α. τ → (∃α. τ)
pack = Λα. λx:τ. ΛR. λf:(∀α. τ→R). f [α] x
```

**Unpack:** Use a hidden type
```
unpack : (∃α. τ) → ∀R. (∀α. τ → R) → R
unpack = λpkg:(∃α. τ). ΛR. λf:(∀α. τ→R). pkg [R] f
```

### Example: Abstract Counter

**Interface:**
```
Counter = ∃State. {
  new  : State,
  inc  : State → State,
  get  : State → Nat
}
```

**Implementation:**
```
makeCounter : Counter
makeCounter = pack [Nat] {
  new = 0,
  inc = λs:Nat. succ s,
  get = λs:Nat. s
}
```

**Using it:**
```
unpack makeCounter as (State, ops) in
  let c0 = ops.new in
  let c1 = ops.inc c0 in
  ops.get c1
```

**Key point:** The client cannot see that State = Nat! The type is hidden (abstract).

---

## Part 11: Impredicativity

### What is Impredicativity?

**Impredicative:** Can quantify over ALL types, including polymorphic ones.

In System F, when we write `∀α. τ`, the α ranges over ALL types, including:
- Base types (Nat, Bool)
- Function types (Nat → Bool)
- Polymorphic types (∀β. β → β)

### Self-Application

This enables amazing things like self-application:

```
id : ∀α. α → α
id = Λα. λx:α. x

selfApp = id [∀β. β → β] id : ∀β. β → β
```

**Step by step:**
1. `id : ∀α. α → α`
2. Instantiate α with `∀β. β → β`:
   ```
   id [∀β. β → β] : (∀β. β → β) → (∀β. β → β)
   ```
3. Apply to id:
   ```
   id [∀β. β → β] id : ∀β. β → β
   ```

### Why This Matters

Impredicativity allows:
- Polymorphic data structures containing polymorphic functions
- Higher-order polymorphic combinators
- Extremely expressive encodings

But it makes type inference undecidable!

### Comparison

| System | Impredicative? | Example |
|--------|----------------|---------|
| **STLC** | No polymorphism | - |
| **Hindley-Milner** | Predicative (Rank-1) | Can't instantiate with ∀ |
| **System F** | Fully impredicative | α can be ANY type, including ∀ |

---

## Part 12: Metatheory

### Strong Normalization

**Theorem:** Every well-typed System F term terminates.

**Proof idea:** Uses **logical relations** - define a predicate "reducible" for each type, and show all well-typed terms are reducible.

**Consequence:** System F is NOT Turing-complete! You cannot write infinite loops.

### Type Safety

**Theorem (Progress):** If `⊢ t : τ` then either:
- t is a value, or
- t → t' for some t'

(Well-typed terms never get stuck)

**Theorem (Preservation):** If `Δ; Γ ⊢ t : τ` and `t → t'`, then `Δ; Γ ⊢ t' : τ`.

(Types are preserved during evaluation)

**Together:** "Well-typed programs don't go wrong"

### Undecidability of Type Inference

**Theorem (Wells, 1999):** Type inference for System F is undecidable.

**What this means:**
- There's no algorithm that can always infer types
- We MUST write type abstractions and applications explicitly
- Local type inference can help (infer some applications)

**Why?** Type inference requires "guessing" type arguments, and there can be infinitely many possibilities.

### Comparison with Other Systems

| System | Terminating? | Type Inference | Expressiveness |
|--------|-------------|----------------|----------------|
| **Untyped LC** | No | N/A | Turing-complete |
| **STLC** | Yes | Decidable | Not Turing-complete |
| **Hindley-Milner** | Yes | Decidable | Not Turing-complete |
| **System F** | Yes | Undecidable | Not Turing-complete (but close!) |

---

## Part 13: System F in the Wild

### Java Generics

Java's generics are inspired by System F:

```java
// Type abstraction (at method level)
public <T> T identity(T x) {
    return x;
}

// Type application (often inferred)
String s = identity("hello");
Integer n = identity(42);
```

**Differences from System F:**
- Type applications usually inferred
- Type erasure at runtime (types disappear!)
- No impredicativity (no `<T>` instantiated with generic type)

### TypeScript

TypeScript has explicit generics closer to System F:

```typescript
// Type abstraction
function identity<T>(x: T): T {
    return x;
}

// Type application (can be explicit)
identity<string>("hello");
identity<number>(42);

// Higher-rank types (with workarounds)
type Id = <T>(x: T) => T;
```

### Haskell

Haskell uses Hindley-Milner by default, but has extensions for higher-rank types:

```haskell
-- Requires RankNTypes extension
id :: forall a. a -> a
id x = x

-- Explicit type application (requires TypeApplications)
id @Bool True
id @Int 5
```

### Rust

Rust's generics are System F-like:

```rust
// Type abstraction
fn identity<T>(x: T) -> T {
    x
}

// Type application (usually inferred)
identity::<String>("hello".to_string());
identity::<i32>(42);
```

### C++ Templates

C++ templates are more like macros, but conceptually similar:

```cpp
// Type abstraction
template <typename T>
T identity(T x) {
    return x;
}

// Type application (often explicit)
identity<std::string>("hello");
identity<int>(42);
```

---

## Summary

You've learned:

1. **Type Abstraction (Λα. t)** - Abstract over types
2. **Type Application (t [τ])** - Apply types to polymorphic terms
3. **Universal Types (∀α. τ)** - Types quantified over all types
4. **Two Contexts (Δ and Γ)** - Track type and term variables separately
5. **Type β-Reduction** - (Λα. t) [τ] → [α ↦ τ]t
6. **Church Encodings** - All data types encodable with ∀
7. **Parametricity** - Polymorphic functions cannot inspect type arguments
8. **Free Theorems** - Derive properties from types alone
9. **Existential Types** - Data abstraction via ∀R. (∀α. τ → R) → R
10. **Impredicativity** - Can quantify over polymorphic types
11. **Strong Normalization** - All programs terminate
12. **Undecidable Inference** - Must write type annotations

System F is the theoretical foundation for generics in modern programming languages. While you rarely write System F directly, understanding it illuminates the design of Java, C#, TypeScript, Rust, and Haskell's type systems.

**Next:** Chapter 6 (System F-omega) adds type operators and a kind system!
