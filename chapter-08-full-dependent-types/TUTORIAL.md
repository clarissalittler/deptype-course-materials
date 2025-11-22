# Chapter 8: Full Dependent Types - Tutorial

## Introduction

Welcome to the final chapter tutorial! This document walks you through the most advanced concepts in type theory: universe hierarchies, propositional equality, inductive families, and the complete Curry-Howard correspondence.

Think of this as your guide from understanding "Type : Type is broken" to "I can use Coq/Agda/Lean to prove theorems!"

This material is challenging. Take it slowly. Work through examples. Don't worry if something doesn't click immediately - dependent type theory takes time to sink in.

---

## Part 1: The Type-in-Type Problem

### What Went Wrong in Chapter 7?

In Chapter 7, we had a beautiful system where terms and types were unified. We could write:
```
Type : Type
```

This seemed elegant - types are first-class values! But there's a fatal flaw...

### Russell's Paradox Revisited

Remember Russell's paradox from set theory?

**Question**: Does the set of "all sets that don't contain themselves" contain itself?

If it does, then by definition it shouldn't. If it doesn't, then by definition it should. Contradiction!

### Girard's Paradox

With `Type : Type`, we can encode a type-level version of Russell's paradox called **Girard's paradox**.

The details are complex, but here's the key insight:
```
If Type : Type, we can construct a term of type Empty
```

This means we can prove False! The entire logical system becomes inconsistent - worthless for proving theorems.

**Why this matters**: If we can prove False, we can prove *anything* (principle of explosion). The system tells us nothing useful.

### The Core Problem

The issue is **impredicativity** - we can quantify over all types to create a type at the same level:

```
Π(A:Type). A → A : Type
```

This lets us construct self-referential types that lead to paradoxes.

### The Solution Preview

We need to **stratify** types into levels:
```
Type 0 : Type 1 : Type 2 : Type 3 : ...
```

This prevents the self-reference that causes paradoxes.

---

## Part 2: Universe Hierarchy

### The Infinite Tower

Instead of one Type, we have infinitely many:

```
Type 0  (small types: Nat, Bool, String, ...)
Type 1  (types of types: Type 0, Nat → Type 0, ...)
Type 2  (bigger types: Type 1, Type 0 → Type 1, ...)
Type 3  (even bigger...)
...
```

**The key rule**:
```
Type i : Type (i+1)
```

Each universe lives in the next one up. This breaks the self-reference.

### Level Examples

Let's compute levels for some types:

**Example 1: `Nat`**
```
Nat : Type 0
```
Nat is a small type - it lives in the first universe.

**Example 2: `Bool → Nat`**
```
Bool : Type 0
Nat : Type 0
Bool → Nat : Type 0
```
A function between small types is still small.

**Example 3: `Type 0`**
```
Type 0 : Type 1
```
The type of small types lives in the next universe up.

**Example 4: `Type 0 → Type 0`**
```
Type 0 : Type 1
Type 0 → Type 0 : Type 1
```
Functions between Type 0's live in Type 1.

### The Pi-Type Level Rule

This is the key rule for dependent functions:

```
If A : Type i  and  B : Type j  (where B may depend on A)
Then Π(x:A). B : Type (max i j)
```

The result lives in the **maximum** of the two levels.

**Example 5: Polymorphic identity (level 0)**
```
id₀ : Π(A:Type 0). A → A

What's the level of this type?
- Type 0 : Type 1
- A : Type 0 (so we're quantifying over Type 1)
- A → A : Type 0 (both sides are Type 0)
- Result: max(1, 0) = Type 1

So: id₀ : Type 1
```

**Example 6: Polymorphic identity (level 1)**
```
id₁ : Π(A:Type 1). A → A

What's the level?
- Type 1 : Type 2
- A : Type 1 (quantifying over Type 2)
- A → A : Type 1
- Result: max(2, 1) = Type 2

So: id₁ : Type 2
```

### Why We Need Multiple Versions

Notice we need both `id₀` and `id₁`:
- `id₀` works on small types (Nat, Bool, etc.)
- `id₁` works on type constructors (Type 0 → Type 0, etc.)

This is a limitation, but it's the price we pay for consistency!

### Practice: Compute Levels

**Exercise 1**: What's the type of `Nat → Bool → Nat`?
<details>
<summary>Answer</summary>

```
Nat : Type 0
Bool : Type 0
Bool → Nat : Type 0
Nat → (Bool → Nat) : Type 0
```
Answer: Type 0
</details>

**Exercise 2**: What's the level of `Π(A:Type 0). Π(B:Type 0). A → B → A`?
<details>
<summary>Answer</summary>

```
Type 0 : Type 1
A : Type 0, B : Type 0 (both quantifying over Type 1)
A → B → A : Type 0
max(1, 1, 0) = 1
```
Answer: Type 1
</details>

**Exercise 3**: Can you apply `id₀` to `Type 0`?
<details>
<summary>Answer</summary>

No! Because:
- `id₀` has type `Π(A:Type 0). A → A`
- `Type 0` has type `Type 1`, not Type 0
- Type mismatch!

You need `id₁` instead:
- `id₁ (Type 0) : Type 0 → Type 0` ✓
</details>

---

## Part 3: Cumulativity

### Making Life Easier

The strict universe hierarchy can be annoying. Consider:

```
we have: x : Nat
and: Nat : Type 0
can we say: x : Type 1?
```

With **cumulativity**, the answer is yes! The rule is:

```
If t : Type i, then t : Type j for any j ≥ i
```

Think of it as: Type 0 ⊆ Type 1 ⊆ Type 2 ⊆ ...

### Benefits

With cumulativity:
```
id₁ : Π(A:Type 1). A → A

Nat : Type 0, but also Nat : Type 1 (by cumulativity)

So we can do: id₁ Nat : Nat → Nat  ✓
```

We only need one polymorphic identity function!

### Trade-offs

**Pros**:
- More convenient to use
- Fewer duplicated definitions
- Closer to mathematical practice

**Cons**:
- More complex type checking
- Harder to implement correctly
- Subtle issues with definitional equality

### Real Systems

- **Coq**: Has cumulativity
- **Agda**: Doesn't have cumulativity (but has universe polymorphism)
- **Our Chapter 8**: No cumulativity (keeps implementation simple)

---

## Part 4: Propositional Equality

### Two Kinds of Equality

Remember from Chapter 7, we had **definitional equality** (written ≡):
```
1 + 1 ≡ 2    (they reduce to the same thing)
```

The type checker knows this automatically. But what about:
```
n + 0 = n    for all n
```

This requires *proof by induction*! The type checker can't figure it out automatically.

### Propositional Equality as a Type

We introduce a new type: **Eq**

```
Eq : Π(A:Type i). A → A → Type i
```

Think of `Eq A x y` as the type of **proofs that x equals y in type A**.

Example types:
```
Eq Nat 2 2           (2 equals 2)
Eq Nat (1+1) 2       (1+1 equals 2)
Eq Nat (n+0) n       (n+0 equals n - needs proof!)
```

### Reflexivity: The Only Constructor

There's exactly one way to construct an equality proof:

```
refl : Π(A:Type i). Π(x:A). Eq A x x
```

This says: any term is equal to itself.

**Example uses**:
```
refl Nat 2 : Eq Nat 2 2  ✓

refl Nat (1+1) : Eq Nat (1+1) (1+1)  ✓
But also: refl Nat 2 : Eq Nat (1+1) 2  ✓
(because 1+1 ≡ 2 definitionally)
```

### When Can We Use refl?

You can use `refl` when both sides are **definitionally equal** - they reduce to the same normal form.

**Works**:
```
refl Nat 2 : Eq Nat (1+1) 2  ✓  (both reduce to 2)
refl Nat 3 : Eq Nat (2+1) (1+2)  ✓  (both reduce to 3)
```

**Doesn't work**:
```
refl Nat ? : Eq Nat (n+0) n  ✗  (doesn't reduce to the same thing)
```

For `n + 0 = n`, we need to *prove* it using induction!

### Where Are Symmetry and Transitivity?

You might ask: "Equality should be symmetric and transitive! Where are those constructors?"

**Answer**: We don't need them as constructors - we can *derive* them using the J eliminator!

---

## Part 5: The J Eliminator

### The Most Powerful Tool

J is the **induction principle for equality**. Its type is intimidating, but incredibly powerful:

```
J : Π(A:Type i).
    Π(x:A).
    Π(C : Π(y:A). Eq A x y → Type i).
    C x (refl x) →
    Π(y:A). Π(eq : Eq A x y). C y eq
```

### Intuitive Understanding

**In plain English**:

"If you want to prove some property C holds for all equalities `x = y`, it's enough to prove it holds for `x = x` with proof `refl x`."

**Why this works**:

The only way to construct `Eq A x y` is with `refl`, which requires `x` and `y` to be the same. So if we can handle the `refl` case, we've handled all cases!

### The Computation Rule

When the equality proof is reflexivity:
```
J A x C p x (refl x)  ~>  p
```

This is the reduction rule that makes J actually compute.

### Example: Deriving Symmetry

Let's prove that equality is symmetric:
```
sym : Π(A:Type). Π(x:A). Π(y:A). Eq A x y → Eq A y x
```

**Step-by-step derivation**:

1. We want to prove: given `x = y`, prove `y = x`

2. Use J with these choices:
   - The property C: `C z eq = Eq A z x`
   - Base case: prove `C x (refl x)` = `Eq A x x`
   - We have: `refl x : Eq A x x` ✓

3. The full term:
```
sym A x y eq = J A x
                 (λz. λeq. Eq A z x)  -- C: property we want
                 (refl x)              -- base case proof
                 y                     -- the other point
                 eq                    -- the equality proof
```

### Let's Trace an Example

Suppose we call `sym Nat 2 2 (refl 2)`:

```
J Nat 2
  (λz. λeq. Eq Nat z 2)
  (refl 2)
  2
  (refl 2)

→ refl 2  (by J's computation rule)
```

And `refl 2 : Eq Nat 2 2` ✓

### Example: Deriving Transitivity

Prove: if `x = y` and `y = z`, then `x = z`

```
trans : Π(A:Type). Π(x y z:A).
        Eq A x y → Eq A y z → Eq A x z
```

**Derivation**:

1. Fix x, and use J to work with `y = z`
2. Property C: given `z` and proof `eq : y = z`, prove `Eq A x z`
3. Base case: when `z = y` and `eq = refl y`, we need `Eq A x y`
4. But we have that! It's our first argument

```
trans A x y z eq1 eq2 =
  J A y
    (λz. λeq. Eq A x z)    -- want to prove x = z
    eq1                     -- when z = y, we have x = y
    z
    eq2
```

### Example: Deriving Congruence

Prove: functions respect equality

```
cong : Π(A B:Type). Π(f:A → B). Π(x y:A).
       Eq A x y → Eq B (f x) (f y)
```

**Derivation**:

1. Given `x = y`, prove `f x = f y`
2. Use J with C: `C z eq = Eq B (f x) (f z)`
3. Base case: prove `Eq B (f x) (f x)` = `refl (f x)`

```
cong A B f x y eq =
  J A x
    (λz. λeq. Eq B (f x) (f z))
    (refl (f x))
    y
    eq
```

### Why J Is Sufficient

These three properties (symmetry, transitivity, congruence) let us prove almost everything about equality!

Every equality proof ultimately breaks down into:
- Using reflexivity
- Using J to transform equalities
- Composing the results

---

## Part 6: Writing Equality Proofs

### Simple Proofs with refl

When both sides compute to the same value:

```
proof1 : Eq Nat (2 + 2) 4
proof1 = refl 4  -- because 2 + 2 ~> 4

proof2 : Eq (Nat → Nat) (λn. n) (λm. m)
proof2 = refl (λn. n)  -- alpha equivalent
```

### Using Symmetry

```
-- Suppose we have: p : Eq Nat a b
-- We can get: sym Nat a b p : Eq Nat b a

example : Eq Nat 5 (2 + 3)
example = sym Nat (2 + 3) 5 (refl 5)
```

### Chaining with Transitivity

```
-- Suppose:
p1 : Eq Nat a b
p2 : Eq Nat b c

-- Then:
trans Nat a b c p1 p2 : Eq Nat a c
```

### Using Congruence

```
-- Suppose: p : Eq Nat n m
-- Then: cong Nat Nat succ n m p : Eq Nat (succ n) (succ m)

example : Eq Nat 3 (1 + 2)
example =
  let p1 : Eq Nat 2 (1 + 1) = refl 2
      p2 : Eq Nat (succ 2) (succ (1 + 1)) = cong Nat Nat succ 2 (1+1) p1
      p3 : Eq Nat 3 (succ 2) = refl 3
  in trans Nat 3 (succ 2) (succ (1+1)) p3 p2
```

### Practice: Write Simple Proofs

**Exercise 1**: Prove `Eq Nat (1 + 2) 3`
<details>
<summary>Answer</summary>

```
proof : Eq Nat (1 + 2) 3
proof = refl 3  -- because 1 + 2 ~> 3
```
</details>

**Exercise 2**: Prove `Eq Nat (succ (succ 0)) 2`
<details>
<summary>Answer</summary>

```
proof : Eq Nat (succ (succ 0)) 2
proof = refl 2  -- both reduce to the same normal form
```
</details>

**Exercise 3**: Given `p : Eq Nat 5 (3 + 2)`, prove `Eq Nat (3 + 2) 5`
<details>
<summary>Answer</summary>

```
proof : Eq Nat (3 + 2) 5
proof = sym Nat 5 (3 + 2) p
```
</details>

---

## Part 7: Inductive Families - Vectors

### From Simple Inductive Types to Families

In previous chapters, we've seen inductive types like:
```
data List (A : Type) where
  Nil  : List A
  Cons : A → List A → List A
```

All constructors return the same type (`List A`).

### Inductive Families: Indices That Vary

An **inductive family** has indices that vary across constructors:

```
data Vec : Nat → Type → Type where
  Nil  : Π(A:Type). Vec 0 A
  Cons : Π(A:Type). Π(n:Nat). A → Vec n A → Vec (succ n) A
```

Notice:
- `Nil` returns `Vec 0 A` (length zero)
- `Cons` takes `Vec n A` and returns `Vec (succ n) A` (length increases by one)

### Parameters vs. Indices

**Parameter** (A): Same for all constructors
- Written before the colon: `Vec (A : Type)`
- Uniform across all constructors

**Index** (n): Varies across constructors
- Written after the colon: `Vec : Nat → Type → Type`
- Different constructors can return different indices

### Working with Vectors

**Creating vectors**:
```
empty : Vec 0 Nat
empty = Nil Nat

one : Vec 1 Nat
one = Cons Nat 0 42 (Nil Nat)

two : Vec 2 Nat
two = Cons Nat 1 17 (Cons Nat 0 42 (Nil Nat))
```

Notice how the index tracks the length!

### Type-Safe Head Function

This is where it gets cool:

```
head : Π(A:Type). Π(n:Nat). Vec (succ n) A → A
head A n (Cons _ _ x xs) = x
```

Notice:
- The type says we need `Vec (succ n) A` - a non-empty vector
- We only pattern match on `Cons` - no `Nil` case!
- The type system **knows** that `Nil : Vec 0 A`, which doesn't match `Vec (succ n) A`
- **Calling head on an empty vector is a type error, not a runtime error!**

### Type-Safe Tail Function

```
tail : Π(A:Type). Π(n:Nat). Vec (succ n) A → Vec n A
tail A n (Cons _ _ x xs) = xs
```

Again, only one case needed. The type system prevents errors!

### Vector Append

The types get really interesting:

```
append : Π(A:Type). Π(m n:Nat).
         Vec m A → Vec n A → Vec (m + n) A
```

The result length is the **sum** of the input lengths!

Implementation sketch:
```
append A m n xs ys = match xs with
  | Nil _ -> ys  -- when m = 0, result is Vec (0 + n) A = Vec n A
  | Cons _ k x xs' ->
      Cons A (k + n) x (append A k n xs' ys)
      -- when m = succ k, result is Vec (succ k + n) A
```

### Why This Matters

Traditional programming:
```javascript
function head(list) {
  if (list.length === 0) throw new Error("Empty list!");
  return list[0];
}
```
Runtime check! Might crash!

With dependent types:
```
head : Vec (succ n) A → A
```
Compile-time guarantee! Cannot crash!

---

## Part 8: Bounded Natural Numbers (Fin)

### The Fin Type

`Fin n` represents natural numbers **strictly less than n**:

```
data Fin : Nat → Type where
  FZ : Π(n:Nat). Fin (succ n)       -- 0 < n+1 for any n
  FS : Π(n:Nat). Fin n → Fin (succ n)  -- if i < n then i+1 < n+1
```

### Counting Inhabitants

**Fin 0**: No constructors work! Empty type.
- `FZ` needs `Fin (succ n)`, but we have `Fin 0`
- `FS` needs a `Fin 0`, but there aren't any!

**Fin 1**: One inhabitant
- `FZ 0 : Fin (succ 0) = Fin 1` ✓
- `FS 0 ?` needs a `Fin 0`, doesn't exist

So `Fin 1 = {0}`

**Fin 2**: Two inhabitants
- `FZ 1 : Fin 2` (represents 0)
- `FS 1 (FZ 0) : Fin 2` (represents 1)

So `Fin 2 = {0, 1}`

**Fin 3**: Three inhabitants
- `FZ 2` (represents 0)
- `FS 2 (FZ 1)` (represents 1)
- `FS 2 (FS 1 (FZ 0))` (represents 2)

So `Fin 3 = {0, 1, 2}`

**Pattern**: `Fin n` has exactly n inhabitants, representing 0, 1, ..., n-1

### Safe Array Indexing

This is the killer application:

```
lookup : Π(A:Type). Π(n:Nat). Vec n A → Fin n → A
```

Read this type carefully:
- Vector has length n
- Index is guaranteed to be less than n
- **Cannot index out of bounds!**

Implementation:
```
lookup A n xs i = match xs with
  | Cons _ k x xs' -> match i with
      | FZ _ -> x  -- first element
      | FS _ i' -> lookup A k xs' i'  -- recurse
```

### Example Usage

```
myVec : Vec 3 Nat
myVec = Cons Nat 2 10 (Cons Nat 1 20 (Cons Nat 0 30 (Nil Nat)))

index0 : Fin 3
index0 = FZ 2  -- represents 0

index1 : Fin 3
index1 = FS 2 (FZ 1)  -- represents 1

result0 : Nat
result0 = lookup Nat 3 myVec index0  -- returns 10

result1 : Nat
result1 = lookup Nat 3 myVec index1  -- returns 20
```

### What About Out of Bounds?

Can we create an index 5 for a vector of length 3?

**No!** Try to construct `Fin 3` representing 5:
- Need `FS 2 (FS 1 (FS 0 ?))`
- The `?` needs to be `Fin 0`
- But `Fin 0` is empty!
- Type error!

The type system prevents the error at compile time!

### Real-World Impact

Languages like Idris use this technique to provide:
- Bounds-checked arrays (at compile time!)
- Safe matrix operations
- Correct-by-construction data structures

---

## Part 9: Eliminators

### What Is an Eliminator?

An eliminator is the **induction principle** for an inductive type. It's the principled way to do recursion in type theory.

### Natural Number Eliminator

```
natElim : Π(P : Nat → Type).
          P zero →
          (Π(k:Nat). P k → P (succ k)) →
          Π(n:Nat). P n
```

**Read this as mathematical induction**:
- To prove `P n` for all `n : Nat`
- Prove base case: `P zero`
- Prove inductive step: `P k` implies `P (succ k)`
- Conclude: `P n` for any `n`

### Reduction Rules

```
natElim P z s zero      ~> z
natElim P z s (succ n)  ~> s n (natElim P z s n)
```

### Example: Addition

```
add : Nat → Nat → Nat
add m n = natElim (λ_. Nat)
                  m                    -- base: 0 + m = m
                  (λk rec. succ rec)   -- step: (k+1) + m = succ (k + m)
                  n
```

Let's trace `add 2 1`:
```
add 2 1
= natElim (λ_. Nat) 2 (λk rec. succ rec) 1
= natElim (λ_. Nat) 2 (λk rec. succ rec) (succ 0)
→ (λk rec. succ rec) 0 (natElim (λ_. Nat) 2 (λk rec. succ rec) 0)
= succ (natElim (λ_. Nat) 2 (λk rec. succ rec) 0)
→ succ 2
= 3
```

### Example: Multiplication

```
mult : Nat → Nat → Nat
mult m n = natElim (λ_. Nat)
                   zero               -- base: 0 * m = 0
                   (λk rec. add m rec)  -- step: (k+1) * m = m + k*m
                   n
```

### Boolean Eliminator

```
boolElim : Π(P : Bool → Type).
           P true →
           P false →
           Π(b:Bool). P b
```

This is like pattern matching:
```
boolElim P t f true   ~> t
boolElim P t f false  ~> f
```

**Example: Boolean AND**:
```
and : Bool → Bool → Bool
and b1 b2 = boolElim (λ_. Bool)
                     b2      -- if b1 is true, return b2
                     false   -- if b1 is false, return false
                     b1
```

### Unit Eliminator

```
unitElim : Π(P : Unit → Type).
           P TT →
           Π(x:Unit). P x
```

There's only one value (`TT`), so only one case:
```
unitElim P u TT ~> u
```

### Empty Eliminator

```
emptyElim : Π(P : Empty → Type).
            Π(e:Empty). P e
```

No reduction rule! There are no values of type `Empty`.

**Example: Principle of Explosion**:
```
exFalso : Π(A:Type). Empty → A
exFalso A e = emptyElim (λ_. A) e
```

This says: from a proof of False, we can prove anything!

### Why Eliminators?

1. **Guaranteed termination**: Eliminators always terminate
2. **Structural recursion**: Can only recurse on structurally smaller arguments
3. **Type safety**: Encoded in the type system
4. **Uniformity**: Every inductive type gets an eliminator

---

## Part 10: Pattern Matching

### Syntactic Sugar

Pattern matching is syntactic sugar for eliminators, but with type refinement:

```
match n with
  | zero -> e1
  | succ k -> e2
```

Desugars to:
```
natElim (λ_. ResultType) e1 (λk _. e2) n
```

### Dependent Pattern Matching

The magic happens when types depend on the matched value:

```
head : Π(A:Type). Π(n:Nat). Vec (succ n) A → A
head A n v = match v with
  | Cons _ _ x xs -> x
  -- No Nil case!
```

Why no `Nil` case?
- We know `v : Vec (succ n) A`
- `Nil` has type `Vec 0 A`
- Since `succ n ≠ 0` for any `n`, the `Nil` case is impossible!
- The type system knows this!

### Coverage Checking

The type checker must verify patterns cover all possible cases:

**Example: Regular matching** (all cases needed)
```
not : Bool → Bool
not b = match b with
  | true -> false
  | false -> true
```

**Example: Dependent matching** (some cases impossible)
```
head : Vec (succ n) A → A
head v = match v with
  | Cons _ _ x xs -> x
  -- Nil case omitted - type system knows it's impossible
```

### Example: Safe Tail

```
tail : Π(A:Type). Π(n:Nat). Vec (succ n) A → Vec n A
tail A n v = match v with
  | Cons _ k x xs -> xs
```

When we match on `Cons`, we learn:
- The vector has shape `Cons _ k x xs`
- So `v : Vec (succ k) A`
- But we also know `v : Vec (succ n) A`
- So `succ k = succ n`, meaning `k = n`
- So `xs : Vec k A = Vec n A` ✓

The type system does this reasoning automatically!

---

## Part 11: Propositions as Types

### The Curry-Howard Correspondence - Complete

We've seen pieces of this before. Now we have the full picture:

| Logic | Type Theory |
|-------|-------------|
| Proposition | Type |
| Proof | Term |
| True (⊤) | Unit |
| False (⊥) | Empty |
| P ∧ Q | Σ(x:P). Q or Pair P Q |
| P ∨ Q | Sum P Q |
| P → Q | Function type P → Q |
| ¬P | P → Empty |
| ∀x. P(x) | Π(x:A). P x |
| ∃x. P(x) | Σ(x:A). P x |
| x = y | Eq A x y |

### Logical Connectives as Types

**True**: The trivially true proposition
```
True : Type
True = Unit

proof : True
proof = TT
```

**False**: The impossible proposition
```
False : Type
False = Empty

-- no proof of False exists!
```

**And (Conjunction)**:
```
And : Type → Type → Type
And P Q = Σ(p:P). Q  -- or simply Pair P Q

-- To prove P ∧ Q, provide:
-- - a proof of P
-- - a proof of Q
```

**Or (Disjunction)**:
```
Or : Type → Type → Type
Or P Q = Either P Q

-- To prove P ∨ Q, provide either:
-- - Left: a proof of P
-- - Right: a proof of Q
```

**Implication**:
```
Implies : Type → Type → Type
Implies P Q = P → Q

-- A proof is a function transforming P-proofs to Q-proofs
```

**Negation**:
```
Not : Type → Type
Not P = P → Empty

-- To prove ¬P, show that P leads to a contradiction
```

**Universal Quantification** (∀):
```
Forall : Π(A:Type). (A → Type) → Type
Forall A P = Π(x:A). P x

-- To prove ∀x. P(x), provide a dependent function
```

**Existential Quantification** (∃):
```
Exists : Π(A:Type). (A → Type) → Type
Exists A P = Σ(x:A). P x

-- To prove ∃x. P(x), provide:
-- - a witness x : A
-- - a proof of P x
```

### Example Proofs

**Modus Ponens**: P ∧ (P → Q) → Q
```
modus_ponens : Π(P Q:Type). P → (P → Q) → Q
modus_ponens P Q p f = f p
```
If we have P and P implies Q, we can conclude Q.

**Double Negation Introduction**: P → ¬¬P
```
double_neg_intro : Π(P:Type). P → Not (Not P)
double_neg_intro P p = λf. f p
```
Given P, assume ¬P for contradiction. Apply ¬P to P to get False.

**Explosion**: ⊥ → P
```
explosion : Π(P:Type). Empty → P
explosion P e = emptyElim (λ_. P) e
```
From False, we can prove anything.

**And Commutativity**: P ∧ Q → Q ∧ P
```
and_comm : Π(P Q:Type). Pair P Q → Pair Q P
and_comm P Q (p, q) = (q, p)
```

**Or Commutativity**: P ∨ Q → Q ∨ P
```
or_comm : Π(P Q:Type). Either P Q → Either Q P
or_comm P Q (Left p)  = Right p
or_comm P Q (Right q) = Left q
```

### The Mind-Bending Part

Every proof is a program! Every program is a proof!

Type checking is proof checking!

This means:
- Compilers can verify mathematical correctness
- Proofs can be executed
- Mathematics and computation are unified

---

## Part 12: Advanced Equality Topics

### Intensional vs. Extensional Equality

Our equality is **intensional**:
```
Eq A x y
```
holds when `x` and `y` are definitionally equal (reduce to the same normal form).

**Example**:
```
f : Nat → Nat
f n = n + 0

g : Nat → Nat
g n = n

-- f and g behave identically on all inputs
-- but: Eq (Nat → Nat) f g  -- CANNOT be proven!
```

Why? Because `f 5 = 5 + 0` doesn't reduce to `5` without proof!

### Extensional Equality

In **extensional** type theory:
```
Function extensionality:
If (∀x. f x = g x), then f = g
```

This makes more things equal, but:
- Type checking becomes undecidable
- We lose canonicity (can't always compute)
- Much harder to implement

Most systems (Agda, Coq) use intensional equality by default, but allow adding function extensionality as an axiom.

### The K Axiom

The K axiom states:
```
K : Π(A:Type). Π(x:A). Π(P : Eq A x x → Type).
    P (refl x) →
    Π(eq : Eq A x x). P eq
```

This says: all proofs of `x = x` are equal to `refl x`.

**Seems reasonable, right?**

### Homotopy Type Theory Rejects K

In **HoTT** (Homotopy Type Theory):
- Types are interpreted as spaces
- Equalities are paths between points
- There can be multiple distinct paths from x to x (loops!)
- K contradicts this interpretation

HoTT provides a new foundation for mathematics where:
- Equality has higher-dimensional structure
- We can reason about paths, homotopies, etc.
- Function extensionality holds naturally

This is cutting-edge research! Check out the HoTT book if you're interested.

---

## Conclusion

Congratulations! You've made it through the most advanced concepts in type theory:

- Universe hierarchy (avoiding paradoxes)
- Propositional equality (J eliminator)
- Inductive families (Vec, Fin)
- Eliminators (principled recursion)
- Pattern matching (type refinement)
- Curry-Howard (complete)

You now understand the foundations of:
- Coq
- Agda
- Lean
- Idris

You're ready to:
- Prove real theorems
- Verify actual programs
- Build certified systems
- Explore advanced type theory

**This is just the beginning of your journey into dependently typed programming and mechanized theorem proving!**

Go forth and prove amazing things! 🎓
