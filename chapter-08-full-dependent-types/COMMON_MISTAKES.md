# Chapter 8: Common Mistakes and How to Avoid Them

## Introduction

Full dependent type theory is the most advanced material in this course. Even experienced programmers make mistakes when learning these concepts. This guide identifies the most common pitfalls and shows you how to avoid them.

**Use this guide**:
- When you get confusing type errors
- When proofs don't type check
- When universe level errors appear
- As a reference while doing exercises
- Before asking for help (check if your issue is here!)

---

## Mistake #1: Universe Level Errors (VERY COMMON)

### The Mistake

**Problem**: Trying to use a type at the wrong universe level.

**Wrong**:
```
id : Π(A:Type 0). A → A
...
id Type 0  ❌  Type error!
```

**Error message**: "Expected Type 0 but got Type 1"

**Why it's wrong**:
- `Type 0` has type `Type 1`, not `Type 0`
- `id` expects an argument of type `Type 0`
- Type mismatch!

### How to Recognize It

You'll see errors like:
- "Universe level mismatch"
- "Expected Type i but got Type j"
- "Cannot apply function at wrong level"

**Common scenario**:
```
-- You wrote
poly_func : Π(A:Type 0). ...

-- Then tried
poly_func (Type 0)  ❌

-- But Type 0 : Type 1, not Type 0!
```

### How to Fix It

**Solution 1**: Use the correct level
```
id₀ : Π(A:Type 0). A → A  -- for small types
id₁ : Π(A:Type 1). A → A  -- for type constructors

id₀ Nat ✓        -- Nat : Type 0
id₁ Type 0 ✓     -- Type 0 : Type 1
```

**Solution 2**: Compute the required level
```
Given: f : Π(A:Type i). ...
To apply to Type j, need: j < i

So if f : Π(A:Type 0). ..., can only apply to terms : Type 0
```

**Solution 3**: Draw the universe hierarchy
```
Type 0 : Type 1 : Type 2 : ...
  ↑        ↑        ↑
 Nat    Type 0   Type 1
Bool    →,Π,Σ
```

### Detection Strategy

When you get a universe error:
1. Check the type of each argument
2. Identify which universe level it lives in
3. Check what the function expects
4. Ensure they match

**Example**:
```
Function: f : Π(A:Type 2). ...
Argument: Type 0
Check: Type 0 : Type 1
Problem: Function wants Type 2, but Type 0 lives in Type 1
Fix: Either change function level or use different argument
```

### Practice Problems

Try these (answers below):
1. Can you apply `id₀ : Π(A:Type 0). A → A` to `Bool → Nat`?
2. Can you apply `id₁ : Π(A:Type 1). A → A` to `Type 0 → Type 0`?
3. What level must `id` be to accept `Type 1` as an argument?

<details>
<summary>Answers</summary>

1. **Yes!** `Bool → Nat : Type 0` ✓
2. **Yes!** `Type 0 → Type 0 : Type 1` ✓
3. `id₂ : Π(A:Type 2). A → A` because `Type 1 : Type 2`
</details>

---

## Mistake #2: Confusing Definitional and Propositional Equality

### The Mistake

**Problem**: Thinking you can use `refl` for any "obviously true" equality.

**Wrong**:
```
proof : Eq Nat (n + 0) n
proof = refl n  ❌  Type error!
```

**Why it's wrong**:
- `n + 0` doesn't reduce to `n` without proof
- `refl` only works for definitional equality
- This requires propositional equality (induction)

### Two Kinds of Equality

**Definitional (≡)**:
- What the type checker knows automatically
- Things that reduce to the same normal form
- Example: `1 + 1 ≡ 2`, `(λx. x) y ≡ y`

**Propositional (Eq)**:
- What you need to prove
- Things that are equal but need induction/reasoning
- Example: `n + 0 = n`, `n + m = m + n`

### How to Recognize It

**Signs you need propositional equality**:
- Involves variables (n, m, etc.)
- Requires induction
- Can't reduce both sides to same form
- Commutativity, associativity, identity laws

**Signs you can use definitional**:
- Concrete numbers: `2 + 3 ≡ 5`
- Beta reduction: `(λx. x) y ≡ y`
- Both sides reduce to same term

### How to Fix It

**When refl works**:
```
proof1 : Eq Nat 2 2
proof1 = refl 2  ✓

proof2 : Eq Nat (1 + 1) 2
proof2 = refl 2  ✓  (1+1 reduces to 2)
```

**When you need a real proof**:
```
add_zero_r : Π(n:Nat). Eq Nat (n + 0) n
add_zero_r = λn.
  natElim (λk. Eq Nat (k + 0) k)
          (refl 0)                    -- base: 0 + 0 = 0
          (λk ih. cong Nat Nat succ (k + 0) k ih)  -- step
          n
```

### Quick Test

Ask yourself: "If I reduce both sides, do I get the same thing without any proof?"
- Yes → Use `refl`
- No → Need propositional proof

### Practice Problems

Which can use `refl`?
1. `Eq Nat (2 + 3) 5`
2. `Eq Nat (n + 0) n`
3. `Eq Nat ((1 + 1) + 1) 3`
4. `Eq Nat (n + m) (m + n)`

<details>
<summary>Answers</summary>

1. **Yes** - `2 + 3` reduces to `5`: `refl 5`
2. **No** - needs induction on `n`
3. **Yes** - reduces to `3`: `refl 3`
4. **No** - needs proof of commutativity
</details>

---

## Mistake #3: Incorrect J Eliminator Usage

### The Mistake

**Problem**: Getting the motive wrong in J.

**Wrong**:
```
sym : Π(A:Type). Π(x y:A). Eq A x y → Eq A y x
sym A x y eq = J A x
                 (λz eq. Eq A x z)  ❌  Wrong motive!
                 (refl x)
                 y eq
```

**Why it's wrong**: The motive gives you `x = z`, but you want `z = x`!

### Understanding the Motive

The motive `C : Π(z:A). Eq A x z → Type` defines what you're trying to prove.

For symmetry, we want: given `x = y`, prove `y = x`

So the motive should be:
```
C z eq = Eq A z x  -- "z equals x"
```

When `z = x` and `eq = refl x`, we need:
```
C x (refl x) = Eq A x x
```
And we have `refl x : Eq A x x` ✓

### How to Build a J Proof

**Step-by-step method**:

1. **Identify the goal**: What are you trying to prove?
   - For sym: given `x = y`, prove `y = x`

2. **Write the motive**: What property should hold for `z` and `eq : x = z`?
   - For sym: `C z eq = Eq A z x`

3. **Check the base case**: What is `C x (refl x)`?
   - For sym: `Eq A x x`

4. **Provide a proof of the base case**:
   - For sym: `refl x : Eq A x x`

5. **Apply J**:
   ```
   J A x (λz eq. Eq A z x) (refl x) y eq
   ```

### Common J Patterns

**Symmetry** (swap endpoints):
```
Motive: C z eq = Eq A z x
Base:   refl x : Eq A x x
```

**Congruence** (apply function):
```
Motive: C z eq = Eq B (f x) (f z)
Base:   refl (f x) : Eq B (f x) (f x)
```

**Substitution** (replace in type):
```
Motive: C z eq = P z
Base:   proof that P x
```

### Practice Problems

Write the motive for:
1. Transitivity: given `x = y` and `y = z`, prove `x = z`
2. Applying a function to both sides of equality

<details>
<summary>Hints</summary>

1. Fix y and z, use J on `eq : x = y`, motive should give `x = z`
2. Motive: `C z eq = Eq B (f x) (f z)`
</details>

---

## Mistake #4: Confusing Parameters and Indices

### The Mistake

**Problem**: Treating indices like parameters in inductive families.

**Wrong conception**:
```
-- Thinking Vec is like this (WRONG):
data Vec (n:Nat) (A:Type) where  ❌
  Nil : Vec n A  -- n is uniform
```

**Correct**:
```
data Vec : Nat → Type → Type where
  Nil  : Vec 0 A           -- index is 0
  Cons : Vec n A → Vec (succ n) A  -- index changes
```

### Parameters vs. Indices

**Parameters**:
- Written before the colon: `List (A:Type)`
- Uniform across all constructors
- Same value in all instances

**Indices**:
- Written after the colon: `Vec : Nat → ...`
- Can vary across constructors
- Different constructors can have different indices

### How to Recognize the Difference

**Ask**: "Does this value change between constructors?"
- Yes → It's an index
- No → It's a parameter

**Examples**:
```
Vec : Nat → Type → Type
      ^^^    ^^^^
    index  parameter

-- Nat is an index (0 for Nil, succ n for Cons)
-- Type is a parameter (same A for both)
```

### Why This Matters

**With indices**, pattern matching refines types:
```
head : Vec (succ n) A → A
head v = match v with
  | Cons _ x xs -> x
  -- Type system knows: can't be Nil because indices don't match!
```

**With parameters**, no refinement:
```
listHead : List A → Maybe A
listHead l = match l with
  | Nil -> Nothing
  | Cons x xs -> Just x
  -- Need both cases - no type-level information about length
```

### Practice Problems

Identify parameters vs. indices:
1. `data Either (A B : Type) : Type where ...`
2. `data Fin : Nat → Type where ...`
3. `data Eq : Π(A:Type). A → A → Type where ...`

<details>
<summary>Answers</summary>

1. A and B are **parameters** (uniform, before colon)
2. Nat is an **index** (varies, after colon)
3. A is a **parameter**, the two A values are **indices** (they vary!)
</details>

---

## Mistake #5: Expecting Pattern Matches to Be Exhaustive When They're Not

### The Mistake

**Problem**: Thinking you can omit cases that are "obviously impossible," but they're not actually impossible.

**Wrong**:
```
getBool : Either Nat Bool → Bool
getBool x = match x with
  | Right b -> b
  -- Oops! Missing Left case  ❌
```

**Error**: "Non-exhaustive pattern match"

### When Can You Omit Cases?

You can **only** omit cases when the **type** makes them impossible:

**Allowed**:
```
head : Vec (succ n) A → A
head v = match v with
  | Cons _ x xs -> x
  -- Can omit Nil because: Nil : Vec 0 A, but we need Vec (succ n) A
  -- Type system knows: 0 ≠ succ n
```

**Not allowed**:
```
maybeHead : Vec n A → Maybe A  ❌
maybeHead v = match v with
  | Cons _ x xs -> Just x
  -- Can't omit Nil! n could be 0
```

### How to Tell If a Case Is Impossible

**Check**: Can the constructor's return type unify with the pattern type?

**Example**:
```
Function type: Vec (succ n) A → ...
Constructor: Nil : Vec 0 A

Can Vec 0 A = Vec (succ n) A?
Can 0 = succ n?
No! (0 is never equal to succ of anything)
→ Case is impossible ✓
```

**Example 2**:
```
Function type: Vec n A → ...
Constructor: Nil : Vec 0 A

Can Vec 0 A = Vec n A?
Can 0 = n?
Yes, when n = 0!
→ Case is possible, must handle ✗
```

### Practice Problems

Which cases can be omitted?
1. `tail : Vec (succ n) A → Vec n A` - can we omit Nil?
2. `isEmpty : Vec n A → Bool` - can we omit Cons?
3. `append : Vec m A → Vec n A → Vec (m + n) A` - what about Nil?

<details>
<summary>Answers</summary>

1. **Yes** - Nil : Vec 0 A doesn't match Vec (succ n) A
2. **No** - n could be non-zero, Cons is possible
3. **No** - m could be 0 (Nil case) or succ k (Cons case), need both
</details>

---

## Mistake #6: Trying to Use General Recursion

### The Mistake

**Problem**: Writing recursive functions that don't structurally decrease.

**Wrong**:
```
-- Trying to write a non-terminating function
loop : Nat
loop = loop  ❌  Rejected!
```

**Why it's wrong**: All functions in dependent type theory must terminate. General recursion would break logical consistency.

### What's Allowed

**Structural recursion only**:
- Must recurse on structurally smaller subterms
- Use eliminators (natElim, boolElim, etc.)
- Pattern matching that compiles to eliminators

**Example (good)**:
```
add : Nat → Nat → Nat
add m n = natElim (λ_. Nat)
                  m                    -- base case
                  (λk rec. succ rec)   -- step: recurse on k (smaller than succ k)
                  n
```

### What's Not Allowed

**Non-structural recursion**:
```
-- Collatz sequence (might not terminate!)
collatz : Nat → Nat
collatz n = if even n
            then collatz (n / 2)  ❌  Not structurally decreasing!
            else collatz (3 * n + 1)
```

**Why rejected**: `3 * n + 1` is larger than `n`, and `n / 2` isn't a direct subterm.

### How to Work Around It

**Option 1**: Prove termination separately (advanced)
**Option 2**: Use well-founded recursion (very advanced)
**Option 3**: Admit the function as an axiom (lose guarantees)
**Option 4**: Restructure to use eliminators

For this course: **stick to eliminators and structural recursion**.

### Detection Strategy

If you get a termination error:
1. Check if you're recursing on a direct subterm
2. If not, try to restructure using eliminators
3. If still stuck, you may be trying to write a non-terminating function

---

## Mistake #7: Wrong Curry-Howard Mapping

### The Mistake

**Problem**: Confusing which type constructor corresponds to which logical connective.

**Wrong**:
```
-- Trying to prove P ∨ Q
and_proof : Pair P Q  ❌  Wrong! That's P ∧ Q
```

### The Correct Mapping

| Logic | Type | Explanation |
|-------|------|-------------|
| P ∧ Q | `Σ(x:P). Q` or `Pair P Q` | Both proofs needed |
| P ∨ Q | `Either P Q` or `Sum P Q` | One proof needed |
| P → Q | `P → Q` | Function from P to Q |
| ¬P | `P → Empty` | P leads to contradiction |
| ∀x. P(x) | `Π(x:A). P x` | Dependent function |
| ∃x. P(x) | `Σ(x:A). P x` | Witness + proof |

### How to Remember

**AND (∧)**: Need both → Pair/Tuple
**OR (∨)**: Need either → Either/Sum
**IMPLIES (→)**: Function type
**NOT (¬)**: To Empty
**FORALL (∀)**: Pi (Π)
**EXISTS (∃)**: Sigma (Σ)

### Common Confusions

**Confusion 1**: ∀ vs. ∃
- ∀ = Pi (Π) - "for all" → function giving proof for each value
- ∃ = Sigma (Σ) - "there exists" → witness + proof

**Confusion 2**: ∧ vs. →
- P ∧ Q = Pair P Q - both proofs
- P → Q = P → Q - function

### Practice Problems

Map these to types:
1. P ∧ (Q ∨ R)
2. ∀x. P(x) → Q(x)
3. ∃x. P(x) ∧ Q(x)
4. ¬(P ∧ Q)

<details>
<summary>Answers</summary>

1. `Pair P (Either Q R)`
2. `Π(x:A). P x → Q x`
3. `Σ(x:A). Pair (P x) (Q x)`
4. `Pair P Q → Empty`
</details>

---

## Mistake #8: Forgetting Universe Annotations

### The Mistake

**Problem**: Not specifying which universe level you're working at.

**Wrong**:
```
id : Π(A:Type). A → A  ❌  Which Type?
```

**Correct**:
```
id₀ : Π(A:Type 0). A → A  ✓
id₁ : Π(A:Type 1). A → A  ✓
```

### Why This Matters

Without specifying the level:
- Ambiguous what types the function accepts
- Can't determine the type of the function itself
- May accidentally use at wrong level

### How to Fix It

**Always specify universe levels**:
```
-- Good
poly : Π(A:Type 0). Π(B:Type 0). (A → B) → A → B

-- Also good (different level)
poly_higher : Π(A:Type 1). Π(B:Type 1). (A → B) → A → B
```

**Compute the level of your function**:
```
id₀ : Π(A:Type 0). A → A

Level of id₀?
- Type 0 : Type 1 (quantifying over Type 1)
- A → A : Type 0
- max(1, 0) = 1
So: id₀ : Type 1
```

---

## Mistake #9: Misunderstanding Fin

### The Mistake

**Problem**: Thinking Fin n contains n, not numbers less than n.

**Wrong conception**:
```
Fin 3 = {0, 1, 2, 3}  ❌
```

**Correct**:
```
Fin 3 = {0, 1, 2}  ✓  (three elements, but largest is 2)
```

### Why This Confuses People

In many languages:
```python
range(3) = [0, 1, 2]  # 3 elements, max is 2
```

But people think:
```
"Fin 3" → "the number 3" ❌
```

Actually:
```
"Fin 3" → "numbers < 3" → {0, 1, 2}
```

### How to Remember

**Fin n has n inhabitants, from 0 to n-1**:
- Fin 0: empty (no numbers < 0)
- Fin 1: {0}
- Fin 2: {0, 1}
- Fin 3: {0, 1, 2}
- Fin n: {0, 1, ..., n-1}

### Why This Matters for Indexing

```
lookup : Vec n A → Fin n → A
```

For `Vec 3 A`:
- Length is 3
- Valid indices: 0, 1, 2
- Type: `Fin 3`
- Perfect match! ✓

---

## Mistake #10: Skipping the Tutorial Examples

### The Mistake

**Problem**: Reading the type signatures but not working through examples.

**Why it's wrong**:
- Dependent types are abstract
- You need concrete examples to build intuition
- Type signatures alone don't show you how things work

### How to Fix It

**For every concept**:
1. Read the definition
2. Work through at least 2-3 examples by hand
3. Try creating your own example
4. Use the REPL to verify

**Example workflow**:
```
1. Read: "natElim is the induction principle for Nat"
2. Study: Example of addition using natElim
3. Work: Trace through add 2 1 step by step
4. Try: Implement multiplication using natElim
5. Verify: Test in REPL
```

### The Examples Matter Most

**For J eliminator**:
- Don't just read the type
- Work through sym step by step
- Then try trans yourself
- Then try cong
- Only then will it click!

**For inductive families**:
- Don't just read the Vec definition
- Create some concrete vectors
- Try head on different vectors
- Understand why Nil case is impossible
- Feel the type refinement

---

## When You're Stuck

### Debugging Checklist

1. **Type error?**
   - Check universe levels
   - Check definitional vs. propositional equality
   - Verify parameter vs. index usage

2. **Pattern match error?**
   - Check if "missing" cases are actually impossible
   - Verify indices match
   - Look at constructor return types

3. **Proof won't type check?**
   - Is it definitionally equal (use refl)?
   - Or propositionally equal (need J)?
   - Check your J motive
   - Verify base case

4. **Eliminator confusion?**
   - Write out the type slowly
   - Identify motive, base case, step
   - Trace through a concrete example
   - Check reduction rules

5. **Still stuck?**
   - Review relevant section in COMMON_MISTAKES.md (you're here!)
   - Check TUTORIAL.md for examples
   - Look at CHEAT_SHEET.md for quick reference
   - Use the REPL to experiment
   - Take a break and come back fresh

---

## Final Advice

**This material is hard**. The smartest people in the world took years to develop these ideas. Don't expect to understand everything immediately.

**Take your time**:
- Work through examples slowly
- Draw diagrams
- Write things out by hand
- Use the REPL constantly
- Review materials multiple times

**It's okay to struggle**:
- The J eliminator is genuinely mind-bending
- Universe levels are subtle
- Inductive families take getting used to
- Everyone finds this challenging

**You've got this**:
- You made it through 7 chapters already
- You understand dependent types from Chapter 7
- This is just adding consistency and power
- With practice, it will click

**Keep going!** 🎓
