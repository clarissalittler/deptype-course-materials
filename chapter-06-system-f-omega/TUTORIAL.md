# Chapter 6: System F-omega (Higher-Kinded Types) - Tutorial

## Introduction

Welcome to System F-omega! In Chapter 5, you learned how to write polymorphic functions that work for any type. In this chapter, we take abstraction one level higher: **types that work for any type constructor**.

**The Big Leap**: Just as System F lets us write one function that works for Bool, Nat, and any other type, System F-omega lets us write one type that works for List, Maybe, Either, and any other type constructor.

This tutorial explains concepts with detailed examples and plain language. Think of it as learning from a tutor who shows you exactly how everything works.

---

## Part 1: Understanding Kinds

### What Are Kinds?

In typed lambda calculus, every term has a type:
```
true : Bool
0 : Nat
λx:Bool. x : Bool → Bool
```

But what "type" does Bool have? Or Nat? Or Bool → Bool?

**Answer**: These don't have types - they have **kinds**. Kinds classify types, just as types classify terms.

```
Bool :: *         (Bool is a proper type)
Nat :: *          (Nat is a proper type)
Bool → Bool :: *  (function types are proper types)
```

The kind `*` (pronounced "star") means "a proper type" - a type that can classify terms.

### Type Constructors

Now consider `List`. What kind does it have?

`List` by itself is NOT a proper type. You can't have a term of type `List` - you need `List Bool` or `List Nat`.

**List takes a type and produces a type**:
```
List Bool :: *    (this is a proper type)
List Nat :: *     (this is a proper type)
```

So what kind is List itself?
```
List :: * → *     (takes a proper type, returns a proper type)
```

### More Examples

**Either takes TWO types**:
```
Either :: * → * → *

Either Bool :: * → *        (partially applied)
Either Bool Nat :: *        (fully applied - a proper type)
```

**A higher-order type constructor**:
Imagine Functor (we'll see this later):
```
Functor :: (* → *) → *
```

This takes a type constructor (something of kind `* → *`) and produces a proper type.

### Visual Intuition

Think of kinds like this:

```
*               : Regular types (Bool, Nat, List Bool)
* → *           : Type constructors taking 1 argument (List, Maybe)
* → * → *       : Type constructors taking 2 arguments (Either, Pair)
(* → *) → *     : Higher-order constructors (Functor, Monad)
```

### Practice Together

**Question**: What kind does `Maybe` have?

Answer: `Maybe` is like `List` - it needs a type argument.
```
Maybe Bool :: *     (proper type)
Maybe :: * → *      (type constructor)
```

**Question**: What's the kind of `Pair`?

Answer: `Pair` needs two type arguments:
```
Pair Bool Nat :: *
Pair :: * → * → *
```

**Question**: What about `Maybe (List Bool)`?

Let's work through this:
1. `Bool :: *` (proper type)
2. `List Bool :: *` (List applied to Bool)
3. `Maybe (List Bool) :: *` (Maybe applied to List Bool)

All proper types have kind `*`!

---

## Part 2: Type-Level Lambda Abstraction

### Type Operators

In System F-omega, we can write **lambda abstractions at the type level**. These are called **type operators**.

**Syntax**: `λα::κ. τ`
- `λ` introduces a type-level lambda
- `α` is the type variable
- `κ` is the kind of α
- `τ` is the body (a type expression)

### Example 1: Identity Type Operator

```
Id = λA::*. A
```

**Reading**: "A type operator that takes a type A and returns A"

**Kind**: What kind does Id have?
- It takes something of kind `*` (that's A)
- It returns something of kind `*` (that's A)
- So: `Id :: * → *`

**Usage**:
```
Id Bool ⟶ Bool
Id Nat ⟶ Nat
Id (Bool → Nat) ⟶ Bool → Nat
```

### Example 2: Constant Type Operator

```
Const = λA::*. λB::*. A
```

**Reading**: "Takes two types A and B, returns A (ignoring B)"

**Kind**:
- Takes `A :: *`
- Takes `B :: *`
- Returns `A :: *`
- So: `Const :: * → * → *`

**Usage**:
```
Const Bool Nat ⟶ Bool
Const (Nat → Nat) Bool ⟶ Nat → Nat
```

### Example 3: Compose Type Operator

This is where it gets interesting!

```
Compose = λF::* → *. λG::* → *. λA::*. F (G A)
```

**Reading**: "Takes two type constructors F and G, and a type A, returns F applied to G applied to A"

**Kind**:
- Takes `F :: * → *` (a type constructor)
- Takes `G :: * → *` (another type constructor)
- Takes `A :: *` (a type)
- Returns `F (G A) :: *` (a proper type)
- So: `Compose :: (* → *) → (* → *) → * → *`

**Usage**:
```
Compose Maybe List Bool
⟶ Maybe (List Bool)
```

This composes `Maybe` and `List`!

### Type-Level Beta Reduction

Just like terms, types can be reduced:

```
(λA::*. A → A) Bool
⟶ Bool → Bool

(λA::*. λB::*. A) Bool Nat
⟶ (λB::*. Bool) Nat
⟶ Bool
```

**Step-by-step for Compose**:
```
Compose Maybe List Bool

= (λF::* → *. λG::* → *. λA::*. F (G A)) Maybe List Bool

⟶ (λG::* → *. λA::*. Maybe (G A)) List Bool     [substitute F ↦ Maybe]

⟶ (λA::*. Maybe (List A)) Bool                  [substitute G ↦ List]

⟶ Maybe (List Bool)                              [substitute A ↦ Bool]
```

### Practice Together

**Example 1**: Reduce `Id (Nat → Nat)`

```
Id (Nat → Nat)
= (λA::*. A) (Nat → Nat)
⟶ Nat → Nat
```

**Example 2**: Reduce `Const Bool (Nat → Nat)`

```
Const Bool (Nat → Nat)
= (λA::*. λB::*. A) Bool (Nat → Nat)
⟶ (λB::*. Bool) (Nat → Nat)
⟶ Bool
```

**Example 3**: What does `Compose List Maybe Nat` normalize to?

```
Compose List Maybe Nat
= (λF::* → *. λG::* → *. λA::*. F (G A)) List Maybe Nat
⟶ (λG::* → *. λA::*. List (G A)) Maybe Nat
⟶ (λA::*. List (Maybe A)) Nat
⟶ List (Maybe Nat)
```

---

## Part 3: Kinding Rules and Derivations

### The Kinding Judgment

The kinding judgment `Γ ⊢ τ :: κ` means:
"Under kind context Γ, type τ has kind κ"

The kind context Γ maps type variables to their kinds:
```
Γ = A::*, B::* → *, C::* → * → *
```

### K-Var: Looking Up Variables

```
α::κ ∈ Γ
─────────  (K-Var)
Γ ⊢ α :: κ
```

**Example**: Given `Γ = A::*, F::* → *`

```
A::* ∈ Γ
──────────  (K-Var)
Γ ⊢ A :: *
```

### K-Arrow: Function Types

```
Γ ⊢ τ₁ :: *    Γ ⊢ τ₂ :: *
──────────────────────────  (K-Arrow)
Γ ⊢ τ₁ → τ₂ :: *
```

**Example**: Kind-check `Bool → Nat`

```
───────────────  (K-Bool)     ──────────────  (K-Nat)
∅ ⊢ Bool :: *                 ∅ ⊢ Nat :: *
─────────────────────────────────────────────  (K-Arrow)
∅ ⊢ Bool → Nat :: *
```

### K-Lam: Type-Level Lambda

```
Γ, α::κ₁ ⊢ τ :: κ₂
─────────────────────────  (K-Lam)
Γ ⊢ λα::κ₁. τ :: κ₁ → κ₂
```

**Example**: Kind-check `λA::*. A → A`

```
Step 1: Check the body under extended context

A::* ∈ {A::*}
──────────────  (K-Var)
A::* ⊢ A :: *

A::* ⊢ A :: *    A::* ⊢ A :: *
────────────────────────────────  (K-Arrow)
A::* ⊢ A → A :: *

Step 2: Apply K-Lam

A::* ⊢ A → A :: *
───────────────────────────  (K-Lam)
∅ ⊢ λA::*. A → A :: * → *
```

**Result**: The identity type operator has kind `* → *` ✓

### K-App: Type Application

```
Γ ⊢ τ₁ :: κ₁ → κ₂    Γ ⊢ τ₂ :: κ₁
────────────────────────────────  (K-App)
Γ ⊢ τ₁ τ₂ :: κ₂
```

**Example**: Kind-check `List Bool`

```
Given: List :: * → *, Bool :: *

───────────────────  (assume)     ───────────────  (K-Bool)
∅ ⊢ List :: * → *                 ∅ ⊢ Bool :: *
──────────────────────────────────────────────────  (K-App)
∅ ⊢ List Bool :: *
```

### Complete Example: Compose

Kind-check: `λF::* → *. λG::* → *. λA::*. F (G A)`

```
Step 1: Start from innermost

Context: Γ = F::* → *, G::* → *, A::*

  Step 1a: Kind-check G A

  G::* → * ∈ Γ              A::* ∈ Γ
  ─────────────  (K-Var)    ──────────  (K-Var)
  Γ ⊢ G :: * → *            Γ ⊢ A :: *
  ────────────────────────────────────  (K-App)
  Γ ⊢ G A :: *

  Step 1b: Kind-check F (G A)

  F::* → * ∈ Γ              Γ ⊢ G A :: *
  ─────────────  (K-Var)
  Γ ⊢ F :: * → *
  ─────────────────────────────────────  (K-App)
  Γ ⊢ F (G A) :: *

Step 2: Apply K-Lam for A

F::* → *, G::* → *, A::* ⊢ F (G A) :: *
────────────────────────────────────────────────  (K-Lam)
F::* → *, G::* → * ⊢ λA::*. F (G A) :: * → *

Step 3: Apply K-Lam for G

F::* → *, G::* → * ⊢ λA::*. F (G A) :: * → *
───────────────────────────────────────────────────────────  (K-Lam)
F::* → * ⊢ λG::* → *. λA::*. F (G A) :: (* → *) → * → *

Step 4: Apply K-Lam for F

F::* → * ⊢ λG::* → *. λA::*. F (G A) :: (* → *) → * → *
──────────────────────────────────────────────────────────────────────  (K-Lam)
∅ ⊢ λF::* → *. λG::* → *. λA::*. F (G A) :: (* → *) → (* → *) → * → *
```

**Result**: `Compose :: (* → *) → (* → *) → * → *` ✓

---

## Part 4: Type-Level Computation

### Type Normalization

Types can be computed using beta reduction, just like terms!

**Example 1**: Simple application
```
(λA::*. A → A) Bool
⟶ [A ↦ Bool](A → A)
⟶ Bool → Bool
```

**Example 2**: Nested application
```
(λA::*. λB::*. A → B) Bool Nat
⟶ (λB::*. Bool → B) Nat
⟶ Bool → Nat
```

**Example 3**: Higher-order application
```
(λF::* → *. λA::*. F A) Maybe Bool
⟶ (λA::*. Maybe A) Bool
⟶ Maybe Bool
```

### Substitution at Type Level

Just like term-level substitution, we substitute type variables:

**[α ↦ τ]σ** means "substitute type τ for type variable α in type σ"

**Examples**:
```
[A ↦ Bool](A → A) = Bool → Bool
[A ↦ Nat](List A) = List Nat
[F ↦ Maybe](F Bool) = Maybe Bool
```

### Complex Example: Compose

```
Compose List Maybe Bool

Full term:
(λF::* → *. λG::* → *. λA::*. F (G A)) List Maybe Bool

Step 1: Apply to List
= (λG::* → *. λA::*. List (G A)) Maybe Bool

Step 2: Apply to Maybe
= (λA::*. List (Maybe A)) Bool

Step 3: Apply to Bool
= List (Maybe Bool)
```

### Practice: What Does This Normalize To?

**Question 1**: `(λA::*. List A) (Nat → Nat)`

<details>
<summary>Answer</summary>

```
(λA::*. List A) (Nat → Nat)
⟶ List (Nat → Nat)
```
</details>

**Question 2**: `(λF::* → *. λA::*. F (F A)) Maybe Bool`

<details>
<summary>Answer</summary>

```
(λF::* → *. λA::*. F (F A)) Maybe Bool
⟶ (λA::*. Maybe (Maybe A)) Bool
⟶ Maybe (Maybe Bool)
```

This applies Maybe twice!
</details>

**Question 3**: `(λA::*. λB::*. Either A B) Bool Nat`

<details>
<summary>Answer</summary>

```
(λA::*. λB::*. Either A B) Bool Nat
⟶ (λB::*. Either Bool B) Nat
⟶ Either Bool Nat
```
</details>

---

## Part 5: Typing with Kinds

### Dual Contexts

Type checking in F-omega uses TWO contexts:

**Γ** (kind context): Maps type variables to kinds
```
Γ = A::*, F::* → *, G::* → * → *
```

**Δ** (type context): Maps term variables to types
```
Δ = x:Bool, y:Nat, f:Nat → Bool
```

The judgment is: `Γ; Δ ⊢ t : τ`
"Under kind context Γ and type context Δ, term t has type τ"

### T-Abs with Kind Checking

```
Γ; Δ, x:τ₁ ⊢ t : τ₂    Γ ⊢ τ₁ :: *
──────────────────────────────────  (T-Abs)
Γ; Δ ⊢ λ(x:τ₁). t : τ₁ → τ₂
```

**Key**: We must check that τ₁ is well-kinded (has kind `*`)!

**Example**: Type-check `λ(x:Bool). x`

```
Step 1: Check Bool is well-kinded

───────────────  (K-Bool)
∅ ⊢ Bool :: *

Step 2: Check body

x:Bool ∈ {x:Bool}
──────────────────────  (T-Var)
∅; x:Bool ⊢ x : Bool

Step 3: Apply T-Abs

∅; x:Bool ⊢ x : Bool    ∅ ⊢ Bool :: *
─────────────────────────────────────  (T-Abs)
∅; ∅ ⊢ λ(x:Bool). x : Bool → Bool
```

### T-TAbs: Type Abstraction

```
Γ, α::κ; Δ ⊢ t : τ
────────────────────────  (T-TAbs)
Γ; Δ ⊢ Λα::κ. t : ∀α::κ. τ
```

**Example**: Type-check `Λα::*. λ(x:α). x`

```
Step 1: Check body under extended kind context

α::* ∈ {α::*}
──────────────  (K-Var)
α::* ⊢ α :: *

α::*; x:α ⊢ x : α    α::* ⊢ α :: *
────────────────────────────────────  (T-Abs)
α::*; ∅ ⊢ λ(x:α). x : α → α

Step 2: Apply T-TAbs

α::*; ∅ ⊢ λ(x:α). x : α → α
──────────────────────────────────────  (T-TAbs)
∅; ∅ ⊢ Λα::*. λ(x:α). x : ∀α::*. α → α
```

This is polymorphic identity!

### T-TApp: Type Application

```
Γ; Δ ⊢ t : ∀α::κ. τ₁    Γ ⊢ τ₂ :: κ
────────────────────────────────────  (T-TApp)
Γ; Δ ⊢ t [τ₂] : [α ↦ τ₂]τ₁
```

**Key**: We must check that τ₂ has the right kind!

**Example**: Type-check `(Λα::*. λ(x:α). x) [Bool]`

```
Step 1: Type the polymorphic function

(From previous example)
∅; ∅ ⊢ Λα::*. λ(x:α). x : ∀α::*. α → α

Step 2: Check Bool has kind *

───────────────  (K-Bool)
∅ ⊢ Bool :: *

Step 3: Apply T-TApp

∅; ∅ ⊢ Λα::*. λ(x:α). x : ∀α::*. α → α    ∅ ⊢ Bool :: *
─────────────────────────────────────────────────────────  (T-TApp)
∅; ∅ ⊢ (Λα::*. λ(x:α). x) [Bool] : Bool → Bool
```

After applying the type, we get the identity function on Booleans!

---

## Part 6: Church-Encoded Type Constructors

### List Type Constructor

In System F-omega, we can define List as a type operator:

```
List = λA::*. ∀R::*. R → (A → R → R) → R
```

**Understanding**:
- Takes a type `A :: *`
- Returns a type `∀R::*. R → (A → R → R) → R`
- This is the "fold" representation of lists!

**Kind**:
```
List :: * → *
```

**Usage**:
```
List Bool = (λA::*. ∀R::*. R → (A → R → R) → R) Bool
          ⟶ ∀R::*. R → (Bool → R → R) → R
```

### List Constructors

**nil**: The empty list
```
nil : ∀A::*. List A
nil = ΛA::*. ΛR::*. λ(n:R). λ(c:A → R → R). n
```

Reading: "For any type A, nil ignores the cons function and returns the nil value"

**cons**: Prepend an element
```
cons : ∀A::*. A → List A → List A
cons = ΛA::*. λ(x:A). λ(xs:List A).
         ΛR::*. λ(n:R). λ(c:A → R → R). c x (xs [R] n c)
```

Reading: "Prepend x to xs by calling c with x and the folded xs"

### Example: Building a List

```
-- List of Booleans: [true, false]
cons [Bool] true (cons [Bool] false (nil [Bool]))

Type: List Bool
Which normalizes to: ∀R::*. R → (Bool → R → R) → R
```

### Maybe Type Constructor

```
Maybe = λA::*. ∀R::*. R → (A → R) → R
```

**Understanding**:
- Takes a type `A :: *`
- Returns: "either nothing (return first R) or just a value (apply function to A)"

**Kind**:
```
Maybe :: * → *
```

### Maybe Constructors

**nothing**: No value
```
nothing : ∀A::*. Maybe A
nothing = ΛA::*. ΛR::*. λ(n:R). λ(j:A → R). n
```

**just**: A value
```
just : ∀A::*. A → Maybe A
just = ΛA::*. λ(x:A). ΛR::*. λ(n:R). λ(j:A → R). j x
```

### Example: Using Maybe

```
-- Maybe Bool representing "Just true"
just [Bool] true

Type: Maybe Bool
Which normalizes to: ∀R::*. R → (Bool → R) → R
```

### Either Type Constructor

```
Either = λA::*. λB::*. ∀R::*. (A → R) → (B → R) → R
```

**Understanding**:
- Takes two types `A :: *` and `B :: *`
- Returns: "either a value of type A (use first function) or type B (use second function)"

**Kind**:
```
Either :: * → * → *
```

### Either Constructors

**left**: Left injection
```
left : ∀A::*. ∀B::*. A → Either A B
left = ΛA::*. ΛB::*. λ(x:A). ΛR::*. λ(l:A → R). λ(r:B → R). l x
```

**right**: Right injection
```
right : ∀A::*. ∀B::*. B → Either A B
right = ΛA::*. ΛB::*. λ(y:B). ΛR::*. λ(l:A → R). λ(r:B → R). r y
```

### Key Insight

All these type constructors:
- Have higher kinds (`* → *` or `* → * → *`)
- Use Church encoding (fold/case-analysis pattern)
- Are first-class citizens in F-omega!

---

## Part 7: Advanced Type Operators

### Flip: Swapping Arguments

```
Flip = λF::* → * → *. λA::*. λB::*. F B A
```

**Usage**:
```
Flip Either Bool Nat
⟶ Either Nat Bool

Flip Pair :: * → * → *
Flip Pair Nat Bool ⟶ Pair Bool Nat
```

### Twice: Applying Twice

```
Twice = λF::* → *. λA::*. F (F A)
```

**Usage**:
```
Twice Maybe Bool
⟶ Maybe (Maybe Bool)

Twice List Nat
⟶ List (List Nat)
```

### Self: Self-Application Type

```
Self = λF::* → *. λA::*. F (F A)
```

This is the same as Twice! It applies a type constructor to itself.

### Practical Example: Nested Structures

Want a list of lists of Booleans?

```
Twice List Bool
⟶ List (List Bool)

Or explicitly:
List (List Bool)
```

Want a Maybe Option (optional optional)?

```
Twice Maybe Nat
⟶ Maybe (Maybe Nat)
```

---

## Part 8: The Functor Pattern

### What is a Functor?

In Haskell, a Functor is a type class:
```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
```

The key insight: `f` has kind `* → *`!

### Functor in F-omega

We can't fully encode type classes, but we can express the kind:

```
Functor :: (* → *) → *
```

This takes a type constructor (like `List` or `Maybe`) and produces... what?

In practice, it would produce evidence/dictionary with the fmap operation.

### Functor for List

If we had type classes, List's functor instance would be:

```
map : ∀A::*. ∀B::*. (A → B) → List A → List B
```

This is the "fmap" for lists.

### Why F-omega Matters for Type Classes

Haskell's type classes work because:
1. Type constructors are first-class (F-omega!)
2. We can abstract over them (higher-kinded polymorphism)
3. Constraints/dictionaries provide implementations

**In Haskell**:
```haskell
class Functor (f :: * -> *) where
  fmap :: (a -> b) -> f a -> f b

instance Functor [] where
  fmap = map

instance Functor Maybe where
  fmap = ...
```

The `f :: * -> *` is pure F-omega!

---

## Part 9: Metatheory

### Strong Normalization

**Theorem**: All type-level reductions in F-omega terminate.

**Why?** The kind system prevents problematic self-application:

```
λA::*. A A   -- INVALID! Can't kind-check

To apply A to itself:
- A must have kind κ₁ → κ₂
- A must have kind κ₁
- But A can't have two different kinds!
```

**Consequence**: Type-level computation always terminates, so kind-checking is decidable.

### Decidable Kind Inference

**Theorem**: Given a type expression, we can algorithmically compute its kind (or report it's ill-kinded).

The algorithm is similar to type inference in STLC.

### Undecidable Type Inference

**Theorem**: Type inference for F-omega (and System F) is undecidable.

**Consequence**: We need type annotations. Most practical languages require:
- Type annotations on lambda parameters
- Explicit type applications in some cases

### Type Safety

**Progress**: Well-typed closed terms don't get stuck.

**Preservation**: Types are preserved during evaluation.

These carry over from System F, with the addition of kind checking ensuring types are well-formed.

---

## Part 10: Real-World Impact

### Haskell: Native Higher-Kinded Types

Haskell's type system is essentially F-omega with extensions:

```haskell
-- Type constructors are first-class
data List a = Nil | Cons a (List a)
-- List :: * -> *

-- Type classes abstract over type constructors
class Functor f where
  fmap :: (a -> b) -> f a -> f b
-- f :: * -> *

-- Kinds are explicit
data Proxy (a :: k) = Proxy
-- Proxy :: forall k. k -> *
```

### Scala: Higher-Kinded Type Parameters

```scala
// F[_] means F has kind * -> *
trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}

// Instances for specific type constructors
implicit val listFunctor: Functor[List] = new Functor[List] {
  def map[A, B](fa: List[A])(f: A => B) = fa.map(f)
}

implicit val optionFunctor: Functor[Option] = new Functor[Option] {
  def map[A, B](fa: Option[A])(f: A => B) = fa.map(f)
}
```

### TypeScript: Limited Support

TypeScript doesn't have true higher-kinded types, but conditional types provide some power:

```typescript
// Can't write Functor<F> where F is a type constructor
// But can do specific instances

type List<A> = A[]
type Maybe<A> = A | null

// Can't abstract over List and Maybe as F
```

### Rust: Associated Types (Partial)

```rust
// Using associated types for similar effect
trait Functor {
    type F<A>;
    fn map<A, B>(fa: Self::F<A>, f: fn(A) -> B) -> Self::F<B>;
}

// But this is more limited than true higher-kinded types
```

### Key Takeaway

F-omega's higher-kinded types are crucial for:
- Generic programming over containers
- Type classes (Functor, Monad, etc.)
- Abstracting over type constructors
- Type-level computation

Modern functional languages rely heavily on these features!

---

## Summary

You've learned:

1. **Kinds** classify types (`*`, `* → *`, `(* → *) → *`)
2. **Type operators** are lambdas at the type level
3. **Kinding rules** ensure types are well-formed
4. **Type-level computation** via beta reduction
5. **Church encodings** for List, Maybe, Either
6. **Advanced operators** like Compose, Flip, Twice
7. **Functor pattern** and connection to type classes
8. **Theoretical properties** (strong normalization, decidability)
9. **Real-world impact** in Haskell, Scala, and beyond

**Next Steps**: Chapter 7 introduces **dependent types**, where types can depend on values (not just other types)! This is the foundation for proof assistants like Coq and Agda.

The journey continues: from untyped → typed → polymorphic → higher-kinded → **dependent**!
