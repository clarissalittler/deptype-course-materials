# Chapter 7: Dependent Types - Tutorial

## Introduction

Welcome to the tutorial for Chapter 7! This is a big conceptual leap: **types can now depend on values**. This might seem strange at first, but it's incredibly powerful.

Think of this tutorial as a patient guide who will show you:
- What it means for types to depend on values
- How Π types generalize function types
- How Σ types generalize product types
- Why types and terms are now unified
- How this enables verified programming

Take your time with each section. This is genuinely new territory, even if you're comfortable with System F.

---

## Part 1: Unified Syntax - Terms and Types Together

### The Big Change

In all previous chapters, we had **separate** syntaxes for terms and types:

**Chapter 2 (STLC)**:
```
Types:  τ ::= Bool | Nat | τ₁ → τ₂
Terms:  t ::= x | λx:τ. t | t₁ t₂ | true | false | ...
```

**Chapter 5 (System F)**:
```
Types:  τ ::= α | τ₁ → τ₂ | ∀α. τ
Terms:  t ::= x | λx:τ. t | t₁ t₂ | Λα. t | t [τ]
```

But in dependent types, **there's only one syntax**:

```
t ::= x | λ(x:t). t | t₁ t₂ | Π(x:t). t | Σ(x:t). t | Type | Nat | Bool | ...
```

Everything is a term! Some terms happen to be types (those whose type is `Type`).

### What Does This Mean?

Let's see some examples:

**Terms that are values**:
```
0 : Nat
true : Bool
λ(x:Nat). x : Nat → Nat
```

**Terms that are types**:
```
Nat : Type
Bool : Type
Nat → Nat : Type
Π(A:Type). A → A : Type
```

**Terms that are type constructors**:
```
λ(A:Type). A → A : Type → Type
```

### The Key Insight

In previous type systems:
- Types were **static** - fixed before runtime
- Terms were **dynamic** - computed at runtime

Now:
- Types **can compute** based on runtime values
- The boundary between types and terms disappears

### Example: Type-Level Function

Let's write a function at the type level:

```
idType : Type → Type
idType = λ(A:Type). A
```

This takes a type and returns it! We can apply it:

```
idType Nat  →  Nat
idType Bool →  Bool
```

The type `idType Nat` **reduces** to `Nat` through β-reduction, just like terms do!

### Practice: Identifying Types vs Terms

For each of these, say whether it's primarily a "type" or a "value":

1. `Nat`
2. `0`
3. `Type`
4. `λ(x:Nat). x`
5. `Nat → Nat`
6. `λ(A:Type). A`

<details>
<summary>Answers</summary>

1. `Nat` - Type (has type `Type`)
2. `0` - Value (has type `Nat`)
3. `Type` - Type (has type `Type` - circular!)
4. `λ(x:Nat). x` - Value (has type `Nat → Nat`)
5. `Nat → Nat` - Type (has type `Type`)
6. `λ(A:Type). A` - Type constructor (has type `Type → Type`)
</details>

---

## Part 2: Pi Types - Dependent Functions

### What's a Pi Type?

The type `Π(x:A). B` is the type of functions that:
- Take an argument `x` of type `A`
- Return a result of type `B`
- **Crucially**: `B` can mention `x`!

That last point is what makes it "dependent" - the return type depends on the argument value.

### Non-Dependent Example

Let's start with something familiar. The simple function type:

```
Nat → Bool
```

This is actually shorthand for:

```
Π(x:Nat). Bool
```

Here `B = Bool` doesn't mention `x`, so it's not dependent. The return type is always `Bool`, regardless of what `x` is.

### Dependent Example 1: Polymorphic Identity

Remember from System F:

```
id : ∀A. A → A
```

In dependent types, we write this as:

```
id : Π(A:Type). A → A
```

Let's break this down:
- The function takes `A : Type` (a type)
- It returns something of type `A → A`
- The return type **mentions A** - it's dependent!

If we apply it:
```
id Nat : Nat → Nat
id Bool : Bool → Bool
```

The return type changes based on the argument!

### Dependent Example 2: Vector Constructor

Here's where it gets really interesting. Imagine a type `Vec : Nat → Type → Type` (we'll see how to define this in Chapter 8).

```
replicate : Π(A:Type). Π(n:Nat). A → Vec n A
```

Let's read this carefully:
- Takes `A : Type` (element type)
- Takes `n : Nat` (length)
- Takes an element of type `A`
- Returns a `Vec n A` (vector of length `n` with elements of type `A`)

The return type `Vec n A` mentions both `A` and `n`! It's doubly dependent.

If we apply it:
```
replicate Nat 3 : Nat → Vec 3 Nat
replicate Bool 5 : Bool → Vec 5 Bool
```

The return type depends on the runtime values `3` and `5`!

### Formation, Introduction, Elimination

Let's see the rules step by step.

**Formation** (How to create a Π type):

To form `Π(x:A). B`, we need:
1. `A` must be a type
2. Assuming `x : A`, we need `B` to be a type
3. Note: `B` can use `x`!

**Introduction** (How to create a value of Π type):

To create something of type `Π(x:A). B`, we write:

```
λ(x:A). t
```

where `t : B` (and `t` can use `x`).

**Example**:
```
λ(A:Type). λ(x:A). x : Π(A:Type). A → A
```

**Elimination** (How to use a value of Π type):

If we have `f : Π(x:A). B` and `a : A`, we can apply:

```
f a : [x ↦ a]B
```

The return type is `B` with `x` replaced by `a`!

**Example**:
```
-- We have:
id : Π(A:Type). A → A
id = λ(A:Type). λ(x:A). x

-- We apply it to Nat:
id Nat : [A ↦ Nat](A → A)
       = Nat → Nat

-- We apply it again to 0:
(id Nat) 0 : [x ↦ 0]Nat
           = Nat
```

### Worked Example: Polymorphic Const

Let's implement polymorphic const step by step.

**Type**:
```
const : Π(A:Type). Π(B:Type). A → B → A
```

Reading: "For all types A and B, give me an A and a B, I'll return the A"

**Implementation**:
```
const = λ(A:Type). λ(B:Type). λ(x:A). λ(y:B). x
```

**Type checking**:
1. `λ(A:Type). ...` - takes a type A
2. `λ(B:Type). ...` - takes a type B
3. `λ(x:A). ...` - takes a value x of type A
4. `λ(y:B). ...` - takes a value y of type B
5. `x` - returns x of type A ✓

**Using it**:
```
const Nat Bool 5 true  →  5
const Bool Nat false 0 →  false
```

### Practice: Polymorphic Compose

Try implementing polymorphic compose yourself:

**Type**:
```
compose : Π(A:Type). Π(B:Type). Π(C:Type). (B → C) → (A → B) → A → C
```

<details>
<summary>Solution</summary>

```
compose = λ(A:Type). λ(B:Type). λ(C:Type). λ(f:B → C). λ(g:A → B). λ(x:A). f (g x)
```

Explanation:
1. Take three types A, B, C
2. Take a function f : B → C
3. Take a function g : A → B
4. Take a value x : A
5. Apply g to x, getting something of type B
6. Apply f to that, getting something of type C ✓
</details>

---

## Part 3: Sigma Types - Dependent Pairs

### What's a Sigma Type?

The type `Σ(x:A). B` is the type of pairs `(a, b)` where:
- `a : A`
- `b : [x ↦ a]B` (the type B with x replaced by a)

The type of the second component **depends on the value** of the first component!

### Non-Dependent Example

The simple product type:

```
Nat × Bool
```

is actually shorthand for:

```
Σ(x:Nat). Bool
```

Here `B = Bool` doesn't mention `x`, so the second component's type is always `Bool`, regardless of the first component's value.

### Dependent Example 1: Type and Value Pair

```
TypeAndValue : Type
TypeAndValue = Σ(A:Type). A
```

This is a pair of:
1. A type `A`
2. A value of type `A`

Examples:
```
(Nat, 0) : TypeAndValue
(Bool, true) : TypeAndValue
(Nat → Nat, λ(x:Nat). x) : TypeAndValue
```

The type of the second component (`A`) depends on the value of the first component!

### Dependent Example 2: Vector with Length

```
VecWithLength : Type → Type
VecWithLength A = Σ(n:Nat). Vec n A
```

This is a pair of:
1. A length `n : Nat`
2. A vector of that length `Vec n A`

Examples:
```
(3, [1, 2, 3]) : VecWithLength Nat
(0, []) : VecWithLength Bool
```

The vector type `Vec n A` depends on the length `n`!

### Projections: Getting Values Out

Given `p : Σ(x:A). B`, we can extract:

**First projection**:
```
fst p : A
```

**Second projection**:
```
snd p : [x ↦ fst p]B
```

Notice: the type of `snd p` depends on the **value** `fst p`!

**Example**:
```
-- We have:
p : Σ(A:Type). A
p = (Nat, 0)

-- First projection:
fst p = Nat : Type

-- Second projection:
snd p : [A ↦ fst p]A
      = [A ↦ Nat]A
      = Nat

snd p = 0 : Nat ✓
```

### Formation, Introduction, Elimination

**Formation** (How to create a Σ type):

To form `Σ(x:A). B`, we need:
1. `A` must be a type
2. Assuming `x : A`, we need `B` to be a type
3. `B` can use `x`

**Introduction** (How to create a value of Σ type):

To create something of type `Σ(x:A). B`, we write:

```
(a, b)
```

where:
- `a : A`
- `b : [x ↦ a]B`

**Elimination** (How to use a value of Σ type):

Given `p : Σ(x:A). B`:
- `fst p : A`
- `snd p : [x ↦ fst p]B`

### Worked Example: Swap

Let's implement a swap function for dependent pairs.

**Type**:
```
swap : Σ(x:Nat). Nat → Σ(y:Nat). Nat
```

(Using non-dependent pairs for simplicity, but the idea works for dependent ones too)

**Implementation**:
```
swap = λ(p:Σ(x:Nat). Nat). (snd p, fst p)
```

**Type checking**:
```
Given: p : Σ(x:Nat). Nat

fst p : Nat
snd p : Nat

(snd p, fst p) : Σ(y:Nat). Nat ✓
```

**Using it**:
```
swap (3, 5) → (5, 3)
swap (0, 1) → (1, 0)
```

### Practice: Dependent Pair Creation

Create a value of type `Σ(A:Type). Σ(B:Type). A × B`:

This is a pair of:
1. A type A
2. A pair of (a type B, a pair of (A, B))

<details>
<summary>Solution</summary>

```
example : Σ(A:Type). Σ(B:Type). A × B
example = (Nat, (Bool, (0, true)))
```

Breakdown:
- First component: `Nat : Type`
- Second component: `(Bool, (0, true)) : Σ(B:Type). Nat × B`
  - First: `Bool : Type`
  - Second: `(0, true) : Nat × Bool`

The types "telescope" - each depends on the previous!
</details>

---

## Part 4: Type Checking with Dependency

### The Typing Judgment

As before, we write:

```
Γ ⊢ t : T
```

meaning "under context Γ, term t has type T".

But now, both `t` and `T` are terms! So we actually type check types too.

### Type Checking a Type

**Example**: Type check `Π(A:Type). A → A`

```
Step 1: Check the whole thing has type Type
We need: ⊢ Π(A:Type). A → A : Type

Step 2: Apply Π-Formation rule
Need: ⊢ Type : Type ✓ (axiom)
Need: A:Type ⊢ A → A : Type

Step 3: Check A → A under A:Type
A:Type ⊢ A → A : Type
This is Π(x:A). A which is okay
⊢ A:Type ⊢ A : Type ✓

Therefore: ⊢ Π(A:Type). A → A : Type ✓
```

### Type Checking a Term

**Example**: Type check `λ(A:Type). λ(x:A). x`

```
Step 1: What type should this have?
Let's derive it bottom-up.

Step 2: The body is λ(x:A). x
Under A:Type, x:A, we have x : A
So: A:Type, x:A ⊢ x : A
Therefore: A:Type ⊢ λ(x:A). x : A → A

Step 3: The whole term
⊢ λ(A:Type). λ(x:A). x : Π(A:Type). A → A ✓
```

### The Conversion Rule (CRUCIAL!)

This is the most important rule for dependent types:

```
Γ ⊢ t : A    A ≡ B    Γ ⊢ B : Type
──────────────────────────────────── (Conv)
Γ ⊢ t : B
```

If:
1. `t` has type `A`
2. `A` is definitionally equal to `B` (they normalize to the same thing)
3. `B` is a valid type

Then `t` also has type `B`.

**Why do we need this?**

Consider:
```
id : Π(A:Type). A → A
id = λ(A:Type). λ(x:A). x

f : Nat → Nat
f = id Nat
```

To type check `f = id Nat`:

```
id Nat : [A ↦ Nat](A → A)
       = Nat → Nat

By Π-Elimination, id Nat : Nat → Nat ✓
```

But we had to **compute** the type! We substituted `Nat` for `A` in `A → A`.

### Worked Example: Polymorphic Identity Application

Type check: `(λ(A:Type). λ(x:A). x) Nat 0`

```
Step 1: Type the identity function
id = λ(A:Type). λ(x:A). x : Π(A:Type). A → A ✓

Step 2: Apply to Nat
id Nat : [A ↦ Nat](A → A)
       = Nat → Nat

Step 3: Apply to 0
(id Nat) 0 : [x ↦ 0]Nat
           = Nat ✓

Step 4: Evaluate
(λ(A:Type). λ(x:A). x) Nat 0
→ (λ(x:Nat). x) 0
→ 0 : Nat ✓
```

### Practice: Type Check Const Application

Type check: `const Nat Bool 5 true`

Where:
```
const : Π(A:Type). Π(B:Type). A → B → A
const = λ(A:Type). λ(B:Type). λ(x:A). λ(y:B). x
```

<details>
<summary>Solution</summary>

```
Step 1: const Nat
const Nat : [A ↦ Nat](Π(B:Type). A → B → A)
          = Π(B:Type). Nat → B → Nat

Step 2: const Nat Bool
const Nat Bool : [B ↦ Bool](Nat → B → Nat)
               = Nat → Bool → Nat

Step 3: const Nat Bool 5
const Nat Bool 5 : [x ↦ 5](Bool → Nat)
                 = Bool → Nat

Step 4: const Nat Bool 5 true
const Nat Bool 5 true : [y ↦ true]Nat
                      = Nat

Step 5: Evaluate
const Nat Bool 5 true
→ (λ(x:Nat). λ(y:Bool). x) 5 true
→ (λ(y:Bool). 5) true
→ 5 : Nat ✓
```
</details>

---

## Part 5: Normalization and Definitional Equality

### What is Definitional Equality?

Two terms `A` and `B` are definitionally equal (`A ≡ B`) if they **normalize to the same value**:

```
A ≡ B  iff  normalize(A) = normalize(B)
```

This includes:
- **α-equivalence**: `λx. x ≡ λy. y` (renaming)
- **β-equivalence**: `(λx. t) s ≡ [x ↦ s]t` (reduction)
- **η-equivalence**: `λx. f x ≡ f` (extensionality, sometimes)

### Why Do We Need This?

Type checking requires comparing types! And types can compute.

**Example**:
```
f : (λ(A:Type). A → A) Nat
```

To type check this, we need to know: what type does `f` have?

```
(λ(A:Type). A → A) Nat  ≡  Nat → Nat
```

We **normalize** the type to compare it:
```
(λ(A:Type). A → A) Nat
→ [A ↦ Nat](A → A)
= Nat → Nat
```

### Normalization Examples

**Example 1**: Simple β-reduction
```
(λ(x:Nat). x) 0
→ [x ↦ 0]x
= 0
```

**Example 2**: Type-level β-reduction
```
(λ(A:Type). A → A) Bool
→ [A ↦ Bool](A → A)
= Bool → Bool
```

**Example 3**: Pair projections
```
fst (3, true)
→ 3

snd (3, true)
→ true
```

**Example 4**: Nested application
```
(λ(A:Type). λ(x:A). x) Nat 0
→ (λ(x:Nat). x) 0
→ 0
```

### When Are Two Types Equal?

**Example 1**: Obviously equal
```
Nat ≡ Nat ✓
Bool ≡ Bool ✓
```

**Example 2**: Equal after normalization
```
(λ(A:Type). A) Nat ≡ Nat ✓

Because:
(λ(A:Type). A) Nat → Nat
Nat → Nat
So they're equal!
```

**Example 3**: Not equal
```
Nat ≢ Bool ✗
Nat → Nat ≢ Nat → Bool ✗
```

### Worked Example: Complex Equality

Are these equal?
```
A: (λ(F:Type → Type). F Nat) (λ(X:Type). X → X)
B: Nat → Nat
```

Let's normalize A:
```
(λ(F:Type → Type). F Nat) (λ(X:Type). X → X)
→ [F ↦ λ(X:Type). X → X](F Nat)
= (λ(X:Type). X → X) Nat
→ [X ↦ Nat](X → X)
= Nat → Nat
```

So:
```
normalize(A) = Nat → Nat
normalize(B) = Nat → Nat
Therefore: A ≡ B ✓
```

### Practice: Normalization

Normalize these:

1. `(λ(A:Type). λ(B:Type). A) Nat Bool`
2. `fst (snd ((1, 2), 3))`
3. `(λ(A:Type). Π(x:A). A) Nat`

<details>
<summary>Solutions</summary>

1. `(λ(A:Type). λ(B:Type). A) Nat Bool`
   ```
   → (λ(B:Type). Nat) Bool
   → Nat
   ```

2. `fst (snd ((1, 2), 3))`
   ```
   → fst 3    (ERROR - 3 is not a pair!)
   ```
   This would be a type error.

3. `(λ(A:Type). Π(x:A). A) Nat`
   ```
   → [A ↦ Nat](Π(x:A). A)
   = Π(x:Nat). Nat
   = Nat → Nat
   ```
</details>

---

## Part 6: Type-Level Computation

### Types Can Compute!

This is the revolutionary idea: types are not just static annotations, they're **programs** that can run.

**Example**: Type constructor
```
Maybe : Type → Type
Maybe = λ(A:Type). Σ(b:Bool). (if b then A else Unit)
```

This is a function at the type level! It takes a type and returns a type.

### Vector Type (Conceptual)

In a full dependent type system (Chapter 8), we can define:

```
Vec : Nat → Type → Type
```

This is a type that depends on a natural number (length) and a type (element type).

**Usage**:
```
Vec 0 Nat      -- vector of 0 Nats
Vec 3 Bool     -- vector of 3 Bools
Vec 10 (Nat → Nat)  -- vector of 10 functions
```

Each of these is a **different type**!

### Safe Head Function

With vectors, we can write:

```
head : Π(n:Nat). Π(A:Type). Vec (succ n) A → A
```

Notice: the vector must have length `succ n`, which is at least 1!

This means `head` can **only be called on non-empty vectors**. The type system guarantees it.

```
head 2 Nat [1, 2, 3] → 1 ✓
head 0 Nat [] → TYPE ERROR! ✓
```

### Append with Length

```
append : Π(m:Nat). Π(n:Nat). Π(A:Type). Vec m A → Vec n A → Vec (m+n) A
```

The return type `Vec (m+n) A` is computed by adding `m` and `n`!

```
append 2 3 Nat [1,2] [3,4,5] : Vec 5 Nat
append 0 3 Bool [] [true, false, true] : Vec 3 Bool
```

The type system knows the result length!

### Type Families

A **type family** is a type that's indexed by values.

Examples:
- `Vec n A` - indexed by length `n`
- `Fin n` - natural numbers less than `n`
- `Sorted : List A → Type` - sorted lists

These let us encode **invariants** in types:
```
lookup : Π(n:Nat). Π(A:Type). Vec n A → Fin n → A
```

Lookup takes an index that's **guaranteed to be in bounds**!

### Worked Example: Type-Level Function

Let's write a type-level function that builds function types:

```
FunType : Nat → Type → Type → Type
FunType = λ(n:Nat). λ(A:Type). λ(B:Type).
  -- Conceptually:
  -- 0 → B
  -- 1 → A → B
  -- 2 → A → A → B
  -- 3 → A → A → A → B
  -- etc.
```

(We'd need full recursion to implement this properly, which comes in Chapter 8)

**Usage**:
```
FunType 0 Nat Bool = Bool
FunType 1 Nat Bool = Nat → Bool
FunType 2 Nat Bool = Nat → Nat → Bool
```

### Practice: Understanding Type Families

Given `Vec : Nat → Type → Type`, answer:

1. What is the type of `Vec 3 Nat`?
2. What is the type of `Vec`?
3. Can you append a `Vec 2 Nat` and a `Vec 3 Nat`?
4. What type would the result have?

<details>
<summary>Answers</summary>

1. `Vec 3 Nat : Type` (it's a type!)
2. `Vec : Nat → Type → Type` (type constructor)
3. Yes! Using `append 2 3 Nat`
4. Result type: `Vec 5 Nat`
</details>

---

## Part 7: Propositions as Types (Curry-Howard)

### The Big Idea

In dependent type theory:
- **Types are propositions**
- **Terms are proofs**
- **Type checking is proof checking**

This is called the **Curry-Howard correspondence**.

### Basic Correspondences

| Logic | Type Theory |
|-------|-------------|
| Proposition P | Type P |
| Proof of P | Term t : P |
| P implies Q | Function type P → Q |
| P and Q | Product type P × Q |
| True | Unit type (has a value) |
| False | Empty type (no values) |

### Example 1: Identity is a Proof

**Proposition**: "For any proposition P, if P is true, then P is true"

**In logic**: P → P

**As a type**: A → A

**Proof/Program**:
```
proof : Π(A:Type). A → A
proof = λ(A:Type). λ(x:A). x
```

This is both:
- A program (identity function)
- A proof (of the proposition)

### Example 2: Const is a Proof

**Proposition**: "If P is true and Q is true, then P is true"

**In logic**: P → Q → P

**As a type**: A → B → A

**Proof/Program**:
```
proof : Π(A:Type). Π(B:Type). A → B → A
proof = λ(A:Type). λ(B:Type). λ(x:A). λ(y:B). x
```

### Dependent Correspondences

| Logic | Type Theory |
|-------|-------------|
| For all x, P(x) | Π(x:A). P(x) |
| Exists x, P(x) | Σ(x:A). P(x) |

### Example 3: Universal Quantification

**Proposition**: "For all types A, there exists a function of type A → A"

**As a type**:
```
Π(A:Type). A → A
```

**Proof/Program**:
```
proof : Π(A:Type). A → A
proof = λ(A:Type). λ(x:A). x
```

This proves: "For every type A, I can give you a function of type A → A" (the identity function).

### Example 4: Existential Quantification

**Proposition**: "There exists a type A and a value of type A"

**As a type**:
```
Σ(A:Type). A
```

**Proof/Program**:
```
proof : Σ(A:Type). A
proof = (Nat, 0)
```

This proves: "I can give you a type (Nat) and a value of that type (0)".

### Worked Example: Transitivity

**Proposition**: "If A implies B, and B implies C, then A implies C"

**In logic**: (A → B) → (B → C) → (A → C)

**As a type**:
```
Π(A:Type). Π(B:Type). Π(C:Type). (A → B) → (B → C) → (A → C)
```

**Proof/Program**:
```
trans : Π(A:Type). Π(B:Type). Π(C:Type). (A → B) → (B → C) → (A → C)
trans = λ(A:Type). λ(B:Type). λ(C:Type). λ(f:A → B). λ(g:B → C). λ(x:A). g (f x)
```

This is function composition! And it's also a proof of transitivity.

### The Deep Connection

When you write a program in dependent type theory, you're **simultaneously**:
1. Writing a program that computes
2. Proving a theorem about that program

**Example**: The type of `head` is a specification:
```
head : Π(n:Nat). Π(A:Type). Vec (succ n) A → A
```

This **proves**: "For any non-empty vector, I can extract the first element"

The implementation is the proof!

### Practice: Propositions as Types

Write types (propositions) and terms (proofs) for:

1. "If we have A, then we have A or B" (where "or" is sum types)
2. "If we have A and B, then we have A"
3. "For all types A and B, if we have A and B, we have B and A"

<details>
<summary>Solutions</summary>

1. ```
   inl : Π(A:Type). Π(B:Type). A → A + B
   inl = λ(A:Type). λ(B:Type). λ(x:A). inj₁ x
   ```

2. ```
   fst : Π(A:Type). Π(B:Type). A × B → A
   fst = λ(A:Type). λ(B:Type). λ(p:A × B). proj₁ p
   ```

3. ```
   swap : Π(A:Type). Π(B:Type). A × B → B × A
   swap = λ(A:Type). λ(B:Type). λ(p:A × B). (snd p, fst p)
   ```
</details>

---

## Part 8: Church Encodings with Dependent Types

### Polymorphic Church Booleans

In Chapter 1, we had:
```
true  = λt. λf. t
false = λt. λf. f
```

With dependent types, we make this **polymorphic**:

```
CBool : Type
CBool = Π(A:Type). A → A → A

ctrue : CBool
ctrue = λ(A:Type). λ(t:A). λ(f:A). t

cfalse : CBool
cfalse = λ(A:Type). λ(t:A). λ(f:A). f
```

Now Church booleans work for **any type**:
```
ctrue Nat 1 0 → 1
ctrue Bool true false → true
cfalse (Nat → Nat) id const → const
```

### Boolean Operations

```
cand : CBool → CBool → CBool
cand = λ(p:CBool). λ(q:CBool). λ(A:Type). λ(t:A). λ(f:A). p A (q A t f) f
```

Explanation:
- If p is true, return q A t f (which is t if q is true, f if q is false)
- If p is false, return f

```
cor : CBool → CBool → CBool
cor = λ(p:CBool). λ(q:CBool). λ(A:Type). λ(t:A). λ(f:A). p A t (q A t f)
```

```
cnot : CBool → CBool
cnot = λ(p:CBool). λ(A:Type). λ(t:A). λ(f:A). p A f t
```

### Polymorphic Church Numerals

```
CNat : Type
CNat = Π(A:Type). (A → A) → A → A

czero : CNat
czero = λ(A:Type). λ(f:A → A). λ(x:A). x

csucc : CNat → CNat
csucc = λ(n:CNat). λ(A:Type). λ(f:A → A). λ(x:A). f (n A f x)
```

Examples:
```
cone : CNat
cone = csucc czero
     = λ(A:Type). λ(f:A → A). λ(x:A). f x

ctwo : CNat
ctwo = csucc cone
     = λ(A:Type). λ(f:A → A). λ(x:A). f (f x)
```

### The Advantage

Polymorphic encodings are **type-safe**! The type system ensures:
- You can't apply a Church boolean to a Church numeral
- You can't add a boolean and a number
- All operations are well-typed

In the untyped lambda calculus, these mistakes compile but behave unpredictably.

---

## Part 9: Type-in-Type and Universes

### The Problem with Type : Type

Our system uses:
```
Type : Type
```

This seems innocent, but it's **logically inconsistent**! It allows proving `False`.

### Girard's Paradox

Similar to Russell's paradox in set theory:
- "The set of all sets that don't contain themselves"

In type theory:
- "The type of all types that don't contain themselves"

With `Type : Type`, we can encode a contradiction.

### Why It's Bad

In a proof assistant, inconsistency means:
- You can prove anything (including false statements!)
- Proofs become meaningless
- The system is useless for verification

### The Solution: Universe Hierarchy

Real dependent type systems use:

```
Type₀ : Type₁ : Type₂ : Type₃ : ...
```

Where:
- `Nat : Type₀`, `Bool : Type₀` (base types)
- `Type₀ : Type₁` (type of types)
- `Nat → Nat : Type₀` (function types)
- `Type₀ → Type₀ : Type₁` (type constructors)

### Rules

1. If `A : Typeᵢ` and `B : Typeⱼ`, then `A → B : Typeₘₐₓ₍ᵢ,ⱼ₎`
2. If `A : Typeᵢ` and `B : Typeⱼ`, then `Π(x:A). B : Typeₘₐₓ₍ᵢ,ⱼ₎`
3. Same for Σ types

### Why We Use Type : Type Anyway

For **pedagogical reasons**:
- Simpler to understand
- Focuses on dependency, not universes
- Real systems (Agda, Coq, Idris) handle this automatically

In Chapter 8, we'll see proper universe hierarchies!

---

## Part 10: Existential Types via Sigma

### Existential Types

An existential type `∃A. T` represents:
- "There exists some type A such that T holds"

We encode this as:
```
∃A. T  =  Σ(A:Type). T
```

### Example 1: Simple Existential

"There exists a type and a value of that type":
```
∃A. A  =  Σ(A:Type). A
```

Values:
```
(Nat, 0) : Σ(A:Type). A
(Bool, true) : Σ(A:Type). A
((Nat → Nat), λ(x:Nat). x) : Σ(A:Type). A
```

### Example 2: Abstract Data Type

"There exists a representation type and operations on it":

```
Counter : Type
Counter = Σ(State:Type). (State × (State → State) × (State → Nat))
```

Components:
1. `State : Type` - the internal representation
2. A pair of:
   - Initial state
   - Increment function
   - Read function

**Implementation using Nat**:
```
natCounter : Counter
natCounter = (Nat, (0, succ, λ(n:Nat). n))
```

**Implementation using Bool** (counts mod 2):
```
boolCounter : Counter
boolCounter = (Bool, (false, not, λ(b:Bool). if b then 1 else 0))
```

The representation is **hidden** inside the Σ type!

### Example 3: Interface

```
Stack : Type → Type
Stack A = Σ(S:Type). (S × (A → S → S) × (S → Nat × A))
```

Components:
1. Stack type `S`
2. Empty stack
3. Push operation
4. Pop operation (returns size and top element)

### Using Existentials

To use an existential package:
```
useCounter : Counter → Nat
useCounter = λ(c:Counter).
  let (State, (init, inc, read)) = c in
  read (inc (inc init))
```

This increments twice and reads, without knowing the internal representation!

---

## Part 11: Theory - Decidability and Normalization

### Type Checking: Decidable ✓

**Question**: Given `Γ`, `t`, and `T`, can we decide if `Γ ⊢ t : T`?

**Answer**: Yes! The algorithm:
1. Check `Γ ⊢ T : Type` (T is a valid type)
2. Infer the type of `t`: compute `T'` such that `Γ ⊢ t : T'`
3. Check if `T ≡ T'` (definitional equality)
4. This requires normalization, which always terminates (strong normalization)

### Type Inference: Undecidable ✗

**Question**: Given `Γ` and `t`, can we infer `T` such that `Γ ⊢ t : T`?

**Answer**: No! Without type annotations on lambdas, inference is undecidable.

**Example**:
```
λx. λy. x
```

What types do x and y have? Could be:
- `Nat → Nat → Nat`
- `Bool → Bool → Bool`
- `Π(A:Type). Π(B:Type). A → B → A`
- Infinitely many others!

So we **require type annotations**:
```
λ(x:Nat). λ(y:Nat). x  -- Inferrable!
```

### Strong Normalization: All Programs Terminate ✓

**Theorem**: Every well-typed term reduces to a normal form in finite steps.

**Consequence**: We can't write:
```
loop = loop
omega = (λx. x x) (λx. x x)
```

These don't type check!

**Trade-off**: Safety vs Expressiveness
- ✓ All programs terminate
- ✗ Can't write general recursion (yet)

We need:
- Structural recursion (Chapter 8)
- Well-founded recursion with termination proofs
- Positive inductive types

### What This Means

In dependent type theory:
- All functions are **total** (defined on all inputs)
- All functions **terminate**
- Type checking is **decidable**
- But we give up general recursion

This makes the system suitable for:
- Theorem proving (proofs must terminate!)
- Verified programming (guarantees termination)
- Type checking (must be decidable)

---

## Summary and Next Steps

### What You've Learned

You now understand:

1. **Unified syntax** - terms and types are the same
2. **Π types** - dependent function types where return type depends on argument
3. **Σ types** - dependent pairs where second type depends on first value
4. **Type-level computation** - types can compute based on values
5. **Curry-Howard** - propositions are types, proofs are programs
6. **Normalization** - crucial for type checking
7. **Type-in-Type** - convenient but inconsistent
8. **Strong normalization** - all programs terminate

### Key Insights

- **Types are first-class**: Types are terms that can compute
- **Dependency is powerful**: Express invariants directly in types
- **Programming is proving**: Writing code is writing proofs
- **Trade-offs matter**: Safety (termination) vs expressiveness (general recursion)

### What's Coming in Chapter 8

- **Inductive families**: Proper Vec, Fin, List definitions
- **Pattern matching**: Structural recursion on inductive types
- **Equality types**: Prove things equal
- **Universe hierarchies**: Fix Type-in-Type
- **Real theorem proving**: Verify properties of programs

This tutorial has given you the foundation. Now you're ready to build verified programs with full dependent types!

---

## Practice Problems - Solutions

Throughout this tutorial, we've included practice problems. Here's a summary of where to find solutions:

- **Part 2**: Polymorphic compose (in solution dropdown)
- **Part 3**: Dependent pair creation (in solution dropdown)
- **Part 4**: Type check const application (in solution dropdown)
- **Part 5**: Normalization exercises (in solution dropdown)
- **Part 6**: Vector type family questions (in solution dropdown)
- **Part 7**: Propositions as types (in solution dropdown)

Work through these to solidify your understanding!

For more practice, see:
- QUIZ.md - Self-check questions with answers
- exercises/EXERCISES.md - Comprehensive exercises
- exercises/Solutions.hs - Complete implementations

Happy learning!
