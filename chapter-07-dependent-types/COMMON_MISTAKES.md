# Chapter 7: Dependent Types - Common Mistakes and How to Avoid Them

## Introduction

Dependent types represent a significant conceptual leap from previous type systems. Even experienced programmers make predictable mistakes when learning them. This guide identifies the most common pitfalls and shows you how to avoid them.

**Use this guide**:
- When type checking fails mysteriously
- When your implementations don't match expected types
- When normalization gives unexpected results
- As a reference while doing exercises

---

## Mistake #1: Confusing Terms and Types

### The Mistake

**Problem**: Trying to use a value where a type is expected, or vice versa.

**Wrong**:
```
-- Using a value as a type
f : 0
f = ...

-- Using a type as a value
x : Nat
x = Bool
```

**Why it's wrong**: Even though terms and types are unified syntactically, they have different roles. A type must have type `Type` (or a universe level).

### How to Recognize It

Look for error messages like:
- "Expected a type, but got a value"
- "0 : Nat, but expected : Type"
- "Cannot use Bool as a value"

**Example**:
```
-- This looks okay at first...
Vec : Nat → Type → Type
v : Vec 3  -- WRONG! Missing the element type
```

### How to Fix It

**Always check**: "Does this have the right type?"

**For types**: Must have type `Type` (or `Typeᵢ`)
```
Nat : Type ✓
Bool : Type ✓
Nat → Bool : Type ✓
```

**For values**: Must have a concrete type
```
0 : Nat ✓
true : Bool ✓
λ(x:Nat). x : Nat → Nat ✓
```

**Correct example**:
```
Vec : Nat → Type → Type
v : Vec 3 Nat  ✓ -- Now complete!
```

### Practice Problems

Identify what's wrong:

1. `f : Π(A:0). A → A`
2. `x : Type; x = 5`
3. `Vec 3 : Type → Type`

<details>
<summary>Answers</summary>

1. `0` is a value (of type Nat), not a type. Should be: `Π(A:Type). A → A`
2. `x : Type` means x is a type, but `5` is a value. Either use `x : Nat` or `x = Nat`
3. `Vec 3` is not fully applied. Should be `Vec 3 Nat : Type` or `Vec 3 : Type → Type`
</details>

---

## Mistake #2: Forgetting to Normalize Types

### The Mistake

**Problem**: Not normalizing types before comparing them, leading to spurious type errors.

**Wrong**:
```
f : (λ(A:Type). A → A) Nat
f = λ(x:Bool). x  -- Type error!
```

**Why it's wrong**: You're trying to use a function of type `Bool → Bool` where `(λ(A:Type). A → A) Nat` is expected. These types **are** equal after normalization, but you forgot to normalize!

### How to Recognize It

Error messages like:
- "Expected type (λ(A:Type). A → A) Nat but got Nat → Nat"
- Types that should be equal aren't recognized as equal
- β-redex in error message

**Example**:
```
id : Π(A:Type). A → A
id = λ(A:Type). λ(x:A). x

-- Using id
f : id Nat  -- What type is this?
```

### How to Fix It

**Always normalize** types that contain:
- Lambda applications
- Pair projections
- Any β-redexes

**Step-by-step normalization**:
```
(λ(A:Type). A → A) Nat
→ [A ↦ Nat](A → A)    -- Substitute
= Nat → Nat            -- Result
```

**Correct example**:
```
f : (λ(A:Type). A → A) Nat
f : Nat → Nat  -- After normalization ✓
f = λ(x:Nat). x
```

### REPL Helper

Use the REPL to normalize types:
```
:normalize (λ(A:Type). A → A) Nat
-- Result: Nat → Nat
```

### Practice Problems

Normalize these types:

1. `(λ(A:Type). Π(x:A). A) Bool`
2. `[A ↦ Nat](A → A → A)`
3. `(λ(F:Type → Type). F Nat) (λ(X:Type). X → X)`

<details>
<summary>Answers</summary>

1. `(λ(A:Type). Π(x:A). A) Bool`
   ```
   → [A ↦ Bool](Π(x:A). A)
   = Π(x:Bool). Bool
   = Bool → Bool
   ```

2. `[A ↦ Nat](A → A → A)`
   ```
   = Nat → Nat → Nat
   ```

3. `(λ(F:Type → Type). F Nat) (λ(X:Type). X → X)`
   ```
   → [F ↦ λ(X:Type). X → X](F Nat)
   = (λ(X:Type). X → X) Nat
   → [X ↦ Nat](X → X)
   = Nat → Nat
   ```
</details>

---

## Mistake #3: Misunderstanding Dependent Application

### The Mistake

**Problem**: Not substituting the argument into the return type when applying a dependent function.

**Wrong**:
```
f : Π(n:Nat). Vec n Nat
f 3 : Vec n Nat  -- WRONG! What's n?
```

**Why it's wrong**: When you apply a dependent function, the parameter gets **substituted** into the return type. You can't leave `n` in the type!

### How to Recognize It

- Free variables in types after application
- Error messages about unbound variables
- Confusion about "what is n?"

**Example**:
```
replicate : Π(A:Type). Π(n:Nat). A → Vec n A
replicate Bool 5 : ???  -- What's the type?
```

### How to Fix It

**Remember the application rule**:
```
If f : Π(x:A). B and a : A
Then f a : [x ↦ a]B  -- Substitute a for x in B!
```

**Step-by-step**:
```
replicate : Π(A:Type). Π(n:Nat). A → Vec n A

replicate Bool : [A ↦ Bool](Π(n:Nat). A → Vec n A)
               = Π(n:Nat). Bool → Vec n Bool

replicate Bool 5 : [n ↦ 5](Bool → Vec n Bool)
                 = Bool → Vec 5 Bool  ✓
```

### Worked Example

```
const : Π(A:Type). Π(B:Type). A → B → A

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
```

### Practice Problems

What are the types after application?

1. `id : Π(A:Type). A → A; id Bool`
2. `head : Π(n:Nat). Vec (succ n) Nat → Nat; head 2`
3. `pair : Π(A:Type). Π(B:Type). A → B → A × B; pair Nat Bool`

<details>
<summary>Answers</summary>

1. `id Bool : [A ↦ Bool](A → A) = Bool → Bool`
2. `head 2 : [n ↦ 2](Vec (succ n) Nat → Nat) = Vec 3 Nat → Nat`
3. `pair Nat Bool : [A ↦ Nat][B ↦ Bool](A → B → A × B) = Nat → Bool → Nat × Bool`
</details>

---

## Mistake #4: Wrong Projection Types for Sigma

### The Mistake

**Problem**: Not understanding that `snd p` has a type that depends on `fst p`.

**Wrong**:
```
p : Σ(A:Type). A
snd p : A  -- WRONG! Which A?
```

**Why it's wrong**: In the type `Σ(A:Type). A`, the second component's type `A` depends on the first component (which is a type). So `snd p` has type "the type that `fst p` is", not just `A`.

### How to Recognize It

- Confusion about projection types
- "Which variable is this?" questions
- Type errors involving dependent pairs

**Example**:
```
p : Σ(n:Nat). Vec n Nat
fst p : Nat
snd p : Vec ??? Nat  -- What goes here?
```

### How to Fix It

**Remember the projection rules**:
```
If p : Σ(x:A). B
Then:
  fst p : A
  snd p : [x ↦ fst p]B  -- Substitute fst p for x in B!
```

**Step-by-step**:
```
p : Σ(n:Nat). Vec n Nat

fst p : Nat  -- The length

snd p : [n ↦ fst p](Vec n Nat)
      = Vec (fst p) Nat  -- A vector of the length from first component!
```

### Worked Example

```
p : Σ(A:Type). A
p = (Nat, 0)

fst p : Type
fst p = Nat

snd p : [A ↦ fst p]A
      = [A ↦ Nat]A
      = Nat  ✓

snd p = 0 : Nat ✓
```

**Another example**:
```
q : Σ(A:Type). Σ(B:Type). A × B
q = (Nat, (Bool, (0, true)))

fst q : Type
fst q = Nat

snd q : [A ↦ fst q](Σ(B:Type). A × B)
      = [A ↦ Nat](Σ(B:Type). A × B)
      = Σ(B:Type). Nat × B

fst (snd q) : Type
fst (snd q) = Bool

snd (snd q) : [B ↦ fst (snd q)](Nat × B)
            = [B ↦ Bool](Nat × B)
            = Nat × Bool

snd (snd q) = (0, true) : Nat × Bool ✓
```

### Practice Problems

Given these pairs, what are the types of the projections?

1. `p : Σ(b:Bool). Nat; fst p : ?; snd p : ?`
2. `q : Σ(A:Type). A → A; fst q : ?; snd q : ?`
3. `r : Σ(n:Nat). Σ(m:Nat). Vec n Nat × Vec m Nat; fst r : ?; snd r : ?`

<details>
<summary>Answers</summary>

1. `fst p : Bool`; `snd p : [b ↦ fst p]Nat = Nat`
2. `fst q : Type`; `snd q : [A ↦ fst q](A → A) = (fst q) → (fst q)`
3. `fst r : Nat`; `snd r : [n ↦ fst r](Σ(m:Nat). Vec n Nat × Vec m Nat) = Σ(m:Nat). Vec (fst r) Nat × Vec m Nat`
</details>

---

## Mistake #5: Ignoring Type-in-Type Inconsistency

### The Mistake

**Problem**: Trying to use our `Type : Type` system for real theorem proving without understanding its limitations.

**Wrong**:
```
-- Trying to prove important theorems
proof : Π(P:Type). P → P
proof = ...

-- This system is inconsistent!
-- Can prove False!
```

**Why it's wrong**: With `Type : Type`, we can encode Girard's paradox and prove `False`, making all proofs meaningless.

### How to Recognize It

You're in danger if:
- You're writing "serious" proofs
- You need logical consistency
- You're trying to verify critical software

**Our system is fine for**:
- Learning dependent types
- Understanding concepts
- Pedagogical purposes

**Our system is NOT suitable for**:
- Real theorem proving
- Verified software development
- Critical applications

### How to Fix It

**For learning**: Use our Type : Type system - it's fine!

**For real work**: Use a proper proof assistant:
- **Agda**: Uses universe levels
- **Coq**: Uses universe hierarchy
- **Idris**: Uses universe levels
- **Lean**: Uses universe hierarchy

**Universe hierarchy** (proper approach):
```
Type₀ : Type₁ : Type₂ : Type₃ : ...

Nat : Type₀
Bool : Type₀
Type₀ : Type₁
(Nat → Nat) : Type₀
(Type₀ → Type₀) : Type₁
```

### What Chapter 8 Will Cover

Chapter 8 introduces proper universe hierarchies and shows how to avoid inconsistency.

---

## Mistake #6: Expecting Type Inference to Work

### The Mistake

**Problem**: Writing lambdas without type annotations and expecting the system to infer types.

**Wrong**:
```
λx. λy. x  -- What are the types of x and y?
```

**Why it's wrong**: Type inference is **undecidable** for dependent types! The system can't guess the types.

### How to Recognize It

Error messages like:
- "Cannot infer type for variable x"
- "Type annotation required"
- "Ambiguous type"

**Example**:
```
f = λx. x  -- What's the type?
-- Could be: Nat → Nat
-- Could be: Bool → Bool
-- Could be: Π(A:Type). A → A
-- Could be infinitely many other types!
```

### How to Fix It

**Always annotate lambda parameters**:

**Wrong**:
```
λx. x
```

**Correct**:
```
λ(x:Nat). x  ✓
λ(x:Bool). x  ✓
λ(A:Type). λ(x:A). x  ✓
```

### Bidirectional Type Checking

Our implementation uses **bidirectional** type checking:
- **Checking mode**: Given a term and an expected type, check if it matches
- **Inference mode**: Given a term, infer its type (limited to simple cases)

**Inference works for**:
- Variables (from context)
- Applications (if function type is known)
- Type-annotated terms

**Inference fails for**:
- Unannotated lambdas
- Complex dependent types
- Ambiguous situations

### Practice: Add Type Annotations

Add annotations to make these type-checkable:

1. `λx. λy. x`
2. `λf. λg. λx. f (g x)`
3. `λp. (snd p, fst p)`

<details>
<summary>Solutions</summary>

1. ```
   λ(x:Nat). λ(y:Bool). x : Nat → Bool → Nat
   -- Or with polymorphism:
   λ(A:Type). λ(B:Type). λ(x:A). λ(y:B). x : Π(A:Type). Π(B:Type). A → B → A
   ```

2. ```
   λ(A:Type). λ(B:Type). λ(C:Type). λ(f:B → C). λ(g:A → B). λ(x:A). f (g x)
   : Π(A:Type). Π(B:Type). Π(C:Type). (B → C) → (A → B) → A → C
   ```

3. ```
   λ(p:Nat × Bool). (snd p, fst p) : Nat × Bool → Bool × Nat
   -- Or with polymorphism:
   λ(A:Type). λ(B:Type). λ(p:A × B). (snd p, fst p) : Π(A:Type). Π(B:Type). A × B → B × A
   ```
</details>

---

## Mistake #7: Confusing Π and Σ

### The Mistake

**Problem**: Using Π where Σ is needed, or vice versa.

**Wrong**:
```
-- Trying to return both a type and a value
package : Π(A:Type). A  -- WRONG! This is a function
```

**Why it's wrong**: Π is for **functions** (dependent or not), Σ is for **pairs** (dependent or not).

### How to Recognize It

**Use Π when**:
- You're defining a function
- You want "for all"
- Input determines output

**Use Σ when**:
- You're creating a pair
- You want "exists"
- You're packaging values together

### Quick Guide

| Want | Use | Example |
|------|-----|---------|
| Function | Π | `Π(A:Type). A → A` |
| For all | Π | `Π(x:Nat). P(x)` |
| Polymorphic function | Π | `Π(A:Type). List A → Nat` |
| Pair | Σ | `Σ(x:Nat). Bool` |
| Exists | Σ | `Σ(A:Type). A` |
| Package with hidden type | Σ | `Σ(S:Type). S × Ops` |

### Examples

**Function (use Π)**:
```
id : Π(A:Type). A → A  ✓
id = λ(A:Type). λ(x:A). x
```

**Package (use Σ)**:
```
package : Σ(A:Type). A  ✓
package = (Nat, 0)
```

**Proposition "for all" (use Π)**:
```
allNatsHaveSuccessor : Π(n:Nat). Nat  ✓
allNatsHaveSuccessor = λ(n:Nat). succ n
```

**Proposition "exists" (use Σ)**:
```
existsANat : Σ(n:Nat). Nat  ✓
existsANat = (0, 0)
```

### Practice: Π or Σ?

Choose Π or Σ for each:

1. A function that takes a type A and returns a value of type A
2. A pair of a natural number and a boolean
3. A proof that there exists a type with a value
4. The polymorphic identity function
5. A vector with its length

<details>
<summary>Answers</summary>

1. **Π**: `Π(A:Type). A` - This is a function!
2. **Σ**: `Σ(n:Nat). Bool` - Though could also be `Nat × Bool`
3. **Σ**: `Σ(A:Type). A` - "Exists" means Σ
4. **Π**: `Π(A:Type). A → A` - Function over all types
5. **Σ**: `Σ(n:Nat). Vec n A` - A pair!
</details>

---

## Mistake #8: Not Understanding Curry-Howard

### The Mistake

**Problem**: Treating types as just type annotations, not as specifications/propositions.

**Missing the point**:
```
head : Π(n:Nat). Vec (succ n) A → A
// "This is just a type annotation"
```

**Missing the insight**:
```
head : Π(n:Nat). Vec (succ n) A → A
// "This PROVES: for any non-empty vector, we can extract the head"
```

### How to Recognize It

You're missing Curry-Howard if you:
- Think types are "just" static annotations
- Don't see the logical meaning
- Wonder why dependent types matter
- Don't understand "proof-relevant programming"

### How to Fix It

**See the double meaning**:

Every type is both:
1. A specification of what values are allowed
2. A proposition that can be proved

Every term is both:
1. A program that computes
2. A proof of its type (as a proposition)

### Examples

**Type**: `A → A`
- **As specification**: "Functions from A to A"
- **As proposition**: "If A is true, then A is true"
- **Term/Proof**: `λ(x:A). x` proves it!

**Type**: `Π(A:Type). A → A`
- **As specification**: "Polymorphic identity function"
- **As proposition**: "For all propositions A, if A then A"
- **Term/Proof**: `λ(A:Type). λ(x:A). x` proves it!

**Type**: `Π(n:Nat). Vec (succ n) A → A`
- **As specification**: "Function that extracts head from non-empty vector"
- **As proposition**: "For any non-empty vector, there exists a first element"
- **Term/Proof**: The implementation of `head` proves it!

**Type**: `Σ(A:Type). A`
- **As specification**: "A pair of a type and a value of that type"
- **As proposition**: "There exists a type A such that A has a value"
- **Term/Proof**: `(Nat, 0)` proves it!

### The Power of This View

When you write:
```
safe_div : Π(m:Nat). Π(n:Nat). (n ≠ 0) → Nat
```

You're simultaneously:
1. Writing a type signature
2. **Proving** that division is safe when the divisor is non-zero
3. The type system **enforces** you can't call it with 0!

This is why dependent types are revolutionary!

---

## Mistake #9: Trying to Write General Recursion

### The Mistake

**Problem**: Trying to write recursive functions like in Chapter 1, forgetting about strong normalization.

**Wrong**:
```
-- Trying to write factorial
fact : Nat → Nat
fact = λ(n:Nat). if iszero n then 1 else n * fact (pred n)
-- ERROR: fact is not in scope (no recursion!)
```

**Why it's wrong**: All well-typed terms **must terminate**! General recursion allows infinite loops, which breaks this property.

### How to Recognize It

- Error messages about undefined variables (recursive calls)
- Wanting to use the Y combinator
- Trying to encode infinite loops

**You cannot write**:
```
loop = loop
omega = (λx. x x) (λx. x x)
Y = λf. (λx. f (x x)) (λx. f (x x))
```

These don't type check!

### How to Fix It

**For this chapter**: Accept the limitation. We can't write general recursion yet.

**For Chapter 8**: Learn about:
- **Structural recursion**: Recursion on inductive types
- **Pattern matching**: Built-in recursion support
- **Well-founded recursion**: Recursion with termination proofs

**Preview of Chapter 8**:
```
-- In Chapter 8, with inductive types
data Nat = Zero | Succ Nat

fact : Nat → Nat
fact Zero = 1
fact (Succ n) = (Succ n) * fact n  -- Structural recursion!
```

The type system can verify this terminates because:
- Each recursive call is on a **smaller** value
- Nat has a well-founded structure
- Eventually we reach Zero (base case)

---

## Mistake #10: Overcomplicating Simple Types

### The Mistake

**Problem**: Using dependent types when simple types suffice.

**Overcomplicated**:
```
const : Π(A:Type). Π(B:Type). A → B → A
const A B x y = x
```

**When you could write**:
```
const : Nat → Bool → Nat
const x y = x
```

**Why it's wrong**: Not every function needs to be polymorphic! Use dependent types when you need dependency, not just for the sake of it.

### How to Recognize It

You're overcomplicating if:
- Every function is Π(A:Type)...
- You don't actually use the dependency
- The code is harder to read
- You're not getting any benefit

### How to Fix It

**Use the simplest type that works**:

**Simple type** (when types are known):
```
add : Nat → Nat → Nat
length : List Nat → Nat
```

**Polymorphic** (when working with any type):
```
id : Π(A:Type). A → A
fst : Π(A:Type). Π(B:Type). A × B → A
```

**Dependent** (when types depend on values):
```
head : Π(n:Nat). Vec (succ n) A → A
replicate : Π(n:Nat). A → Vec n A
```

### Decision Guide

Ask yourself:
1. Do I need to work with any type? → Use Π(A:Type)
2. Does the return type depend on a value? → Use Π(x:A). B
3. Am I packaging values where types depend? → Use Σ(x:A). B
4. Otherwise → Use simple types!

---

## Summary: Quick Reference

### When You Get Stuck

1. **Type Error?**
   - Check if you're confusing terms and types (Mistake #1)
   - Try normalizing types (Mistake #2)
   - Verify you've substituted correctly in Π application (Mistake #3)

2. **Projection Confusion?**
   - Remember `snd p : [x ↦ fst p]B` (Mistake #4)
   - Draw out the types step by step

3. **Can't Write Recursion?**
   - Remember strong normalization (Mistake #9)
   - Wait for Chapter 8!

4. **Type Inference Failing?**
   - Add type annotations to all lambdas (Mistake #6)
   - Use bidirectional type checking

5. **Π vs Σ Confusion?**
   - Π for functions, Σ for pairs (Mistake #7)
   - Π for "for all", Σ for "exists"

### Before Moving to Chapter 8

Make sure you understand:
- ✓ The difference between Π and →
- ✓ The difference between Σ and ×
- ✓ How normalization works
- ✓ How to substitute in dependent types
- ✓ Curry-Howard correspondence basics
- ✓ Why Type : Type is problematic
- ✓ Why general recursion doesn't work

If you're still making these mistakes, review:
- TUTORIAL.md for detailed explanations
- LESSON_PLAN.md for structured learning
- QUIZ.md to test your understanding
- exercises/EXERCISES.md for practice

Good luck, and remember: dependent types are hard! Take your time, work through examples, and don't get discouraged.
