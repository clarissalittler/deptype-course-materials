# Chapter 6: System F-omega - Common Mistakes and How to Avoid Them

## Introduction

System F-omega introduces kinds and type-level computation, which opens up new categories of mistakes. This guide identifies the most common pitfalls and shows you how to avoid them.

**Use this guide**:
- When your kinds don't match up
- When type operators don't normalize as expected
- When kinding derivations fail mysteriously
- As a reference while doing exercises

---

## Mistake #1: Confusing Kinds with Types (THE BIG ONE)

### The Mistake

**Problem**: Treating kinds and types as the same thing.

**Wrong thinking**:
```
"Bool is a type, so it has type *"  ❌
```

**Correct thinking**:
```
"Bool is a type, so it has KIND *"  ✓
```

### Why It's Confusing

We have three levels now:
1. **Terms** have **types** (e.g., `true : Bool`)
2. **Types** have **kinds** (e.g., `Bool :: *`)
3. **Kinds** have... nothing (they're the top level)

| Level | Example | Classified By |
|-------|---------|---------------|
| Terms | `true`, `0`, `λx:Bool. x` | Types |
| Types | `Bool`, `Nat`, `List Bool` | Kinds |
| Kinds | `*`, `* → *` | Nothing (primitive) |

### How to Fix It

**Always ask**: "Am I talking about a term, type, or kind?"

- Use `:` for term-to-type: `true : Bool`
- Use `::` for type-to-kind: `Bool :: *`
- Never say "type of a type" - say "kind of a type"

### Practice Problems

What's wrong with these statements?

1. "The type of `Bool` is `*`"
2. "List has type `* → *`"
3. "`Maybe Bool : *`"

<details>
<summary>Answers</summary>

1. **Wrong**: Should say "The KIND of `Bool` is `*`"
2. **Wrong**: Should say "List has KIND `* → *`"
3. **Wrong**: Should say "`Maybe Bool :: *`" (double colon for kinds)

Remember: Types have kinds, not types!
</details>

---

## Mistake #2: Wrong Kind for Type Constructors

### The Mistake

**Problem**: Thinking type constructors like `List` have kind `*`.

**Wrong**:
```
List :: *   ❌
```

**Correct**:
```
List :: * → *   ✓
```

### Why This Matters

`List` by itself is NOT a proper type! You can't have a term of type `List`:

```
x : List   ❌  INVALID!

x : List Bool   ✓  Valid!
```

### The Rule

Only **fully applied** type constructors have kind `*`:

| Type Expression | Kind | Is it a proper type? |
|----------------|------|---------------------|
| `List` | `* → *` | No - needs an argument |
| `List Bool` | `*` | Yes - fully applied |
| `Either` | `* → * → *` | No - needs two arguments |
| `Either Bool` | `* → *` | No - needs one more |
| `Either Bool Nat` | `*` | Yes - fully applied |

### How to Recognize

**If it needs type parameters, its kind is NOT `*`!**

```
List _____      needs 1 parameter  →  kind * → *
Either _____ _____  needs 2 parameters  →  kind * → * → *
Maybe _____     needs 1 parameter  →  kind * → *
```

### Practice Problems

What are the kinds of these?

1. `Bool`
2. `Nat → Bool`
3. `Maybe`
4. `Maybe (List Bool)`
5. `λA::*. A → A`

<details>
<summary>Answers</summary>

1. `Bool :: *` (proper type)
2. `Nat → Bool :: *` (proper type - function types are proper types)
3. `Maybe :: * → *` (needs a type argument)
4. `Maybe (List Bool) :: *` (fully applied - proper type)
5. `λA::*. A → A :: * → *` (type operator taking a type)
</details>

---

## Mistake #3: Type Application Kind Mismatch

### The Mistake

**Problem**: Applying a type operator to an argument of the wrong kind.

**Wrong**:
```
List Maybe   ❌

Why? List :: * → * expects a type of kind *
     But Maybe :: * → *, not *
```

**Correct**:
```
List Bool   ✓  (Bool :: *)
List (Maybe Bool)   ✓  (Maybe Bool :: *)
```

### How to Recognize

When applying `F τ`:
1. Check: What kind is `F`? Must be `κ₁ → κ₂`
2. Check: What kind is `τ`? Must be `κ₁`
3. Result: `F τ` has kind `κ₂`

### Example: Why `List Maybe` Fails

```
Step 1: Kind of List?
List :: * → *

Step 2: Kind of Maybe?
Maybe :: * → *

Step 3: Can we apply?
List expects kind *
Maybe has kind * → *
* ≠ * → *  ❌  KIND MISMATCH!
```

### Correct Example: `List (Maybe Bool)`

```
Step 1: Kind of Maybe Bool?
Maybe :: * → *
Bool :: *
Maybe Bool :: *  ✓

Step 2: Can we apply List?
List :: * → *
Maybe Bool :: *
* = *  ✓  MATCHES!

Result: List (Maybe Bool) :: *
```

### How to Fix

**Always check kinds match in applications!**

Use K-App rule:
```
Γ ⊢ τ₁ :: κ₁ → κ₂    Γ ⊢ τ₂ :: κ₁
────────────────────────────────  (K-App)
Γ ⊢ τ₁ τ₂ :: κ₂
```

The domain kind of τ₁ must match the kind of τ₂!

### Practice Problems

Which of these are well-kinded?

1. `Maybe Bool`
2. `Maybe (List Nat)`
3. `List Either`
4. `List (Either Bool Nat)`
5. `(λF::* → *. F Bool) Maybe`

<details>
<summary>Answers</summary>

1. **Well-kinded** - `Maybe :: * → *`, `Bool :: *` ✓
2. **Well-kinded** - `List Nat :: *` so `Maybe (List Nat) :: *` ✓
3. **Ill-kinded** - `Either :: * → * → *`, not `*` ❌
4. **Well-kinded** - `Either Bool Nat :: *` ✓
5. **Well-kinded** - `λF::* → *. F Bool` expects `* → *`, `Maybe :: * → *` ✓
</details>

---

## Mistake #4: Forgetting Kind Annotations

### The Mistake

**Problem**: Writing type lambdas without kind annotations.

**Wrong**:
```
λA. A → A   ❌  What kind is A?
```

**Correct**:
```
λA::*. A → A   ✓  A has kind *
```

### Why It Matters

Without kind annotations, we don't know what A represents:
- If `A :: *`, then `λA::*. A` is a simple type operator
- If `A :: * → *`, then `λA::* → *. A` is a higher-order operator

### The Rule

**Always annotate type variables with their kinds!**

```
λα::κ. τ   (NOT λα. τ)
```

### Examples

**Wrong**:
```
Compose = λF. λG. λA. F (G A)   ❌  Missing all kind annotations!
```

**Correct**:
```
Compose = λF::* → *. λG::* → *. λA::*. F (G A)   ✓
```

### How to Determine the Kind

Ask: "What am I applying this variable to, or what's applied to it?"

```
λF::?. λA::?. F A

- F is applied to A
- So F must be a function kind: F :: * → *
- A is an argument to F
- F expects kind *, so: A :: *

Result: λF::* → *. λA::*. F A
```

### Practice Problems

Add kind annotations:

1. `λA. A`
2. `λA. λB. Either A B`
3. `λF. λA. F (F A)`

<details>
<summary>Answers</summary>

1. `λA::*. A :: * → *` (simple identity)
2. `λA::*. λB::*. Either A B :: * → * → *`
3. `λF::* → *. λA::*. F (F A) :: (* → *) → * → *` (applies F twice!)
</details>

---

## Mistake #5: Type-Level Variable Capture

### The Mistake

**Problem**: Same as term-level variable capture, but at the type level!

**Wrong**:
```
[A ↦ F](λF::* → *. F A)  ?

Naively substituting:
λF::* → *. F F   ❌  WRONG! Free A became bound by λF
```

**Correct** (with α-conversion):
```
[A ↦ F](λF::* → *. F A)

Step 1: Rename bound variable
λF::* → *. F A  →  λG::* → *. G A

Step 2: Substitute safely
[A ↦ F](λG::* → *. G A) = λG::* → *. G F   ✓
```

### Why It Happens

Type-level substitution follows the same rules as term-level substitution!

### The Rule

Before substituting `[α ↦ τ]σ`:
1. Check if `τ` has free type variables
2. Check if `σ` has type lambdas binding those variables
3. If yes: α-convert first!

### Example Walkthrough

```
[F ↦ Maybe](λF::* → *. λA::*. F A)

Danger! We're substituting Maybe (which contains F... wait, no it doesn't)

Actually safe:
= λF::* → *. λA::*. F A  (F is bound, not affected)
```

But this is dangerous:
```
[A ↦ F](λF::* → *. A)

Step 1: Recognize F is free in what we're substituting
Step 2: Recognize λF binds F in the target
Step 3: α-convert

λF::* → *. A  →  λG::* → *. A

Step 4: Substitute
[A ↦ F](λG::* → *. A) = λG::* → *. F   ✓
```

### Practice Problems

Perform these substitutions correctly:

1. `[A ↦ Bool](λA::*. A)`
2. `[A ↦ F](λF::* → *. F A)`
3. `[F ↦ List](λA::*. F A)`

<details>
<summary>Answers</summary>

1. `λA::*. A` (A is bound, not substituted - shadowing!)
2. Need α-conversion: `λG::* → *. G F`
3. `λA::*. List A` (F is free, safe to substitute)
</details>

---

## Mistake #6: Normalizing Too Early or Too Late

### The Mistake

**Problem**: Not knowing when to normalize type expressions.

**Confusion**:
```
Is (λA::*. A) Bool the same as Bool?
```

**Answer**: They're **equal** (beta-equivalent) but not **identical**.

### When to Normalize

**During kind checking**: Types should be normalized
```
Check: List ((λA::*. A) Bool)

Normalize: (λA::*. A) Bool ⟶ Bool
Then: List Bool :: *   ✓
```

**During type checking**: Types should be normalized and compared
```
Check: Does τ₁ = τ₂?

Normalize both, then compare:
(λA::*. A) Bool =?= Bool
Bool =?= Bool   ✓
```

### The Rule

**Always normalize before comparing types!**

### Example

```
Are these the same type?
- (λA::*. λB::*. A) Bool Nat
- Bool

Normalize:
(λA::*. λB::*. A) Bool Nat
⟶ (λB::*. Bool) Nat
⟶ Bool

Yes, they're the same!  ✓
```

### Practice Problems

Normalize these:

1. `(λA::*. A → A) (Nat → Bool)`
2. `(λF::* → *. λA::*. F A) List Bool`
3. `(λA::*. λB::*. A) (List Nat) Bool`

<details>
<summary>Answers</summary>

1. `(Nat → Bool) → (Nat → Bool)`
2. `List Bool`
3. `List Nat` (Const returns first argument)
</details>

---

## Mistake #7: Misunderstanding Church Encodings

### The Mistake

**Problem**: Not understanding that Church-encoded types are type-level lambdas.

**Confusion**:
```
List = λA::*. ∀R::*. R → (A → R → R) → R

Wait, is this a type or a type operator?
```

**Answer**: It's a **type operator** (kind `* → *`)!

### Understanding the Encoding

```
List :: * → *

When applied:
List Bool :: *
```

The type `List Bool` normalizes to:
```
∀R::*. R → (Bool → R → R) → R
```

This is the type of the fold operation!

### Key Insight

```
Type Constructor:  List = λA::*. ...
Kind:              List :: * → *

Applied Type:      List Bool
Kind:              List Bool :: *
Normalized:        ∀R::*. R → (Bool → R → R) → R
```

### Common Confusion

**Wrong thinking**: "List Bool is a type constructor"
**Correct**: "List is a type constructor, List Bool is a type"

| Expression | Kind | What is it? |
|------------|------|-------------|
| `List` | `* → *` | Type constructor (needs argument) |
| `List Bool` | `*` | Type (can classify terms) |
| `nil [Bool]` | `List Bool` | Term (has type) |

### Practice Problems

For each, identify if it's a type constructor (needs arguments) or a proper type:

1. `Maybe`
2. `Maybe Nat`
3. `Either`
4. `Either Bool Nat`
5. `λA::*. List A`

<details>
<summary>Answers</summary>

1. Type constructor - `Maybe :: * → *`
2. Proper type - `Maybe Nat :: *`
3. Type constructor - `Either :: * → * → *`
4. Proper type - `Either Bool Nat :: *`
5. Type constructor - `λA::*. List A :: * → *` (eta-equivalent to List)
</details>

---

## Mistake #8: Applying Functor Reasoning Incorrectly

### The Mistake

**Problem**: Thinking F-omega has full type class support.

**Wrong**:
```
"I can define Functor in F-omega just like Haskell!"   ❌
```

**Reality**:
```
"I can define the KIND of Functor, but not the full type class system"   ✓
```

### What F-omega Gives Us

**Can express**:
- The kind of Functor: `(* → *) → *`
- Type constructors: `List :: * → *`, `Maybe :: * → *`
- Higher-kinded polymorphism: `∀F::* → *. ...`

**Cannot express** (without extensions):
- Type class constraints
- Instance selection
- Coherence (one instance per type)

### Example

**What we can write**:
```
-- Type constructor
List :: * → *

-- Polymorphic map (for a specific type constructor)
map : ∀A::*. ∀B::*. (A → B) → List A → List B
```

**What we can't write** (without extensions):
```
-- Generic functor (needs type classes)
class Functor (f :: * → *) where
  fmap :: ∀A::*. ∀B::*. (A → B) → f A → f B
```

### Why Haskell Needs F-omega

Haskell's type classes build ON TOP of F-omega:
1. F-omega provides higher-kinded types
2. Type classes add constraints and instances
3. Result: Functor, Monad, etc.

### The Key Difference

| Feature | F-omega | Haskell |
|---------|---------|---------|
| Higher-kinded types | ✓ Yes | ✓ Yes |
| Type constructors | ✓ Yes | ✓ Yes |
| Type operators | ✓ Yes | ✓ Yes (type families) |
| Type classes | ✗ No | ✓ Yes |
| Instance resolution | ✗ No | ✓ Yes |

---

## Summary of Common Mistakes

### The Top 5 Mistakes

1. **Confusing kinds with types** - Remember: types have kinds (not types)
2. **Wrong kinds for type constructors** - `List :: * → *`, not `List :: *`
3. **Kind mismatches in application** - Always check kinds match
4. **Forgetting kind annotations** - Always write `λα::κ. τ`
5. **Type-level variable capture** - α-convert at type level too!

### Quick Reference: What to Check

When writing type operators:
- [ ] Are all type variables annotated with kinds?
- [ ] Do kinds match in applications?
- [ ] Have I normalized before comparing?
- [ ] Am I avoiding variable capture?

When working with Church encodings:
- [ ] Do I understand what kind the encoding has?
- [ ] Do I know when it's a type vs type constructor?
- [ ] Have I fully applied it to get a proper type?

### Debugging Strategy

When something goes wrong:

1. **Check kinds first** - Most errors are kind mismatches
2. **Write out derivations** - Build the kinding derivation step by step
3. **Normalize types** - Reduce type expressions before comparing
4. **Draw it out** - Visual diagrams help with higher-order kinds
5. **Use the REPL** - Experiment with type normalization

### Signs You're Getting It

You know you understand F-omega when:
- You instinctively think about kinds
- You can explain why `List Maybe` is ill-kinded
- Type-level lambda feels natural
- You see the connection to Haskell/Scala
- You understand what "higher-kinded" means

Keep practicing! These concepts are challenging but incredibly powerful once they click.

---

## Additional Resources

### If You're Still Struggling

1. **Draw kind diagrams**: Visualize `*`, `* → *`, `(* → *) → *`
2. **Practice with simple examples**: Start with `Id`, `Const` before `Compose`
3. **Compare with System F**: See what's new vs what's the same
4. **Use the REPL**: Experiment constantly
5. **Review TUTORIAL.md**: Step-by-step walkthroughs

### Practice Exercises

From exercises/EXERCISES.md, focus on:
- Exercise 1: Basic type operators (builds intuition)
- Exercise 2-4: Church encodings (practical application)
- Exercise 6: Type-level computation (deeper understanding)

Master these before moving to advanced challenges!
