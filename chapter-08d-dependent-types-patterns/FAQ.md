# Chapter 8: Full Dependent Types - Frequently Asked Questions

## Table of Contents

1. [Universe Hierarchy](#universe-hierarchy)
2. [Propositional Equality](#propositional-equality)
3. [J Eliminator](#j-eliminator)
4. [Inductive Families](#inductive-families)
5. [Eliminators](#eliminators)
6. [Comparison Questions](#comparison-questions)
7. [Practical Proving](#practical-proving)
8. ["I'm Stuck" Scenarios](#im-stuck-scenarios)
9. [Advanced Topics](#advanced-topics)

---

## Universe Hierarchy

### Q1: Why do we need universe levels?

**A**: To avoid the **Type-in-Type paradox** from Chapter 7!

```
Chapter 7: Type : Type    ✗ Allows Girard's paradox
Chapter 8: Type : Type1    ✓ Consistent!
           Type1 : Type2
           Type2 : Type3
           ...
```

**Infinite tower** prevents circular definitions that could prove false.

### Q2: What exactly is a universe?

**A**: A **type of types**:

```
Nat : Type         (Nat is a small type)
Bool : Type        (Bool is a small type)
Type : Type1       (Type itself is a larger type)
Type1 : Type2      (Type1 is even larger)
```

**Intuition**: Sets form a hierarchy
- Type 0: Small sets (Nat, Bool, ...)
- Type 1: Collections of small sets
- Type 2: Collections of Type 1 things
- ...

### Q3: How do I know which universe level to use?

**A**: **Rule**: If you're quantifying over `Typeᵢ`, result lives in `Typeᵢ₊₁`:

```
Nat : Type             (level 0)
Nat → Bool : Type      (level 0, both inputs are Type)

Π(A:Type). A : Type1   (quantify over Type, so level 1)

Π(A:Type1). A : Type2  (quantify over Type1, so level 2)
```

**In practice**: Let the type checker infer levels!

### Q4: Can I write universe-polymorphic functions?

**A**: In advanced systems, yes! Example:

```
id : Π(i:Level). Π(A:Typeᵢ). A → A
```

Works at ANY universe level!

In this chapter: Usually stick to specific levels for simplicity.

### Q5: What's "predicativity"?

**A**: Universe hierarchy is **predicative**:

- Quantifying over Type gives Type1 (not Type)
- Can't have "set of all sets" at same level

**Impredicative** (System F):
- `∀A. A → A : *` even though it quantifies over `*`

**Impredicative paradoxes**: Not possible in predicative hierarchy
**Trade-off**: More complex, but consistent!

---

## Propositional Equality

### Q6: What's the difference between definitional and propositional equality?

**A**:

**Definitional equality** (Chapter 7):
- Things that normalize to same term
- `2 + 2` and `4` are definitionally equal
- Type checker checks automatically

**Propositional equality** (Chapter 8):
- Type `Eq A x y` - proofs that x = y
- Need to CONSTRUCT proofs
- `n + 0 = n` requires induction proof!

```
2 + 2 = 4               Definitional (free)
n + 0 = n               Propositional (must prove!)
```

### Q7: What is the Eq type?

**A**: Type of **equality proofs**:

```
Eq A x y : Type

"The type of proofs that x equals y in type A"
```

Example:
```
Eq Nat 0 0          (type of proofs that 0 = 0)
refl 0 : Eq Nat 0 0 (the proof itself)
```

**Key**: Eq is a TYPE (proposition), proofs are TERMS!

### Q8: Why do we need both kinds of equality?

**A**:

**Definitional**: For type checking
```
(\(x:Nat). x) 3 : Nat
Type checker: (\(x:Nat). x) 3 reduces to 3, which is Nat ✓
```

**Propositional**: For proving
```
Prove: Π(n:Nat). n + 0 = n

Can't use definitional (doesn't compute that way)
NEED propositional equality proof!
```

**Definitional** = mechanical reduction
**Propositional** = mathematical reasoning

### Q9: How do I construct equality proofs?

**A**: Three ways:

1. **Reflexivity** (trivial case):
   ```
   refl x : Eq A x x
   ```

2. **J eliminator** (general case):
   ```
   Use J to derive from refl
   ```

3. **Other eliminators** (specific types):
   ```
   nat Elim, boolElim, etc.
   ```

**All non-trivial proofs ultimately use J!**

### Q10: What does refl really mean?

**A**: **Reflexivity** - everything equals itself:

```
refl : Π(A:Type). Π(x:A). Eq A x x
```

It's the ONLY constructor of Eq!

**Key insight**: ALL equality proofs are "essentially" refl
- Either directly `refl x`
- Or derived from refl via J

This is the foundation of equality reasoning!

---

## J Eliminator

### Q11: What is the J eliminator (simply)?

**A**: **Principle of equality induction**:

"To prove property P for ALL equality proofs,
 it suffices to prove P for refl"

```
J : Π(A:Type).
    Π(C:Π(x:A). Π(y:A). Eq A x y → Type).  -- Motive
    Π(c:Π(x:A). C x x (refl x)).           -- Base case (refl)
    Π(x:A). Π(y:A). Π(p:Eq A x y).        -- Inputs
    C x y p                                 -- Result
```

If it holds for `refl`, it holds for ALL equalities!

### Q12: How do I use J in practice?

**A**: Template:

```
J A                                    -- Type
  (\(x:A). \(y:A). \(eq:Eq A x y). ...) -- What to prove (motive)
  (\(z:A). ...)                        -- Proof for refl case
  x y proof                            -- Apply to specific x, y, proof
```

Example - symmetry:
```
sym : Π(A:Type). Π(x:A). Π(y:A). Eq A x y → Eq A y x
sym = \(A:Type). \(x:A). \(y:A). \(eq:Eq A x y).
  J A
    (\(a:A). \(b:A). \(e:Eq A a b). Eq A b a)  -- Goal: swap
    (\(z:A). refl z)                            -- refl z : Eq A z z (symmetric!)
    x y eq
```

### Q13: Why is J so confusing?

**A**: It's abstract! Tips:

1. **The motive** `C` says WHAT you're proving
   ```
   For sym: "If x = y, then y = x"
   Motive: \(x). \(y). \(eq:Eq A x y). Eq A y x
   ```

2. **The base case** proves it for `refl`
   ```
   For sym: refl z : Eq A z z is its own symmetry!
   ```

3. **J automatically** extends to all proofs

**Intuition**: Since all proofs reduce to refl, proving for refl is enough!

### Q14: Can all equality reasoning be done with J?

**A**: **YES!** J is complete for equality reasoning:

- **Symmetry**: x = y → y = x ✓
- **Transitivity**: x = y → y = z → x = z ✓
- **Congruence**: x = y → f x = f y ✓
- **Substitution**: x = y → P x → P y ✓

Everything derivable from J!

### Q15: What's the K axiom and do we have it?

**A**: **K axiom**: All proofs of `x = x` are `refl x`

```
K : Π(A:Type). Π(x:A). Π(p:Eq A x x). p = refl x
```

**In this chapter**: Usually YES (intensional equality)
**In HoTT** (Homotopy Type Theory): NO!

K makes some reasoning easier but is controversial in modern type theory.

---

## Inductive Families

### Q16: What's an inductive family?

**A**: Inductive type **indexed by values**:

```
Vec : Type → Nat → Type
      ↑       ↑
      param   index

Vec A 0   -- Empty vector
Vec A 3   -- Vector with exactly 3 elements
```

Index (Nat) changes between constructors!

Compare to:
```
List A -- All lists have same type
```

### Q17: Why are Vec and Fin important?

**A**: **Vec** - length-indexed lists:
```
Vec A n : Type    "List of exactly n elements"

vnil : Vec A 0
vcons : A → Vec A n → Vec A (n+1)
```

**Prevents out-of-bounds errors!**

**Fin** - bounded naturals:
```
Fin n : Type      "Natural numbers less than n"

Fin 3 has exactly 3 inhabitants: 0, 1, 2
```

**Perfect for array indexing!**

### Q18: How do I pattern match on inductive families?

**A**: Use **eliminators** (covered below) or **dependent pattern matching** (if available):

```
vecElim : Π(A:Type).
          Π(C:Π(n:Nat). Vec A n → Type).   -- Motive
          C 0 (vnil A) →                    -- Nil case
          (Π(n:Nat). Π(x:A). Π(xs:Vec A n). C n xs → C (n+1) (vcons A n x xs)) →
          Π(n:Nat). Π(v:Vec A n). C n v
```

Like natElim but for vectors!

### Q19: Can I define my own inductive families?

**A**: In full systems (Agda, Coq), yes!

In this chapter: Usually work with provided ones:
- **Nat**: Natural numbers
- **Bool**: Booleans
- **Vec**: Vectors
- **Fin**: Finite sets
- **Empty**: Empty type

To add more, need to extend the core system.

### Q20: What's the "large elimination" restriction?

**A**: **Large elimination**: Eliminating into Type (not just values)

Example:
```
boolElim : Π(C:Bool → Type). ...
                   ↑ Returns Type, not value!
```

Some systems restrict this for consistency reasons. 

In this chapter: Usually allowed (intensional type theory).

---

## Eliminators

### Q21: What are eliminators and why use them?

**A**: **Eliminators** are the official way to do recursion/induction:

**natElim** - Recursion on Nat:
```
natElim C base step n
  C : Nat → Type    -- What you're computing
  base : C 0        -- Base case
  step : Π(k:Nat). C k → C (k+1)  -- Inductive step
  n : Nat          -- Input
```

**Why not pattern matching?** Eliminators:
- Work in ANY system (even without pattern matching)
- Make induction principle explicit
- Guarantee termination

### Q22: How do I use natElim to define functions?

**A**: Example - addition:

```
add : Nat → Nat → Nat
add = \(m:Nat). \(n:Nat).
  natElim
    (\(_:Nat). Nat)           -- Motive: always Nat
    n                         -- add 0 n = n
    (\(k:Nat). \(rec:Nat). succ rec)  -- add (k+1) n = succ (add k n)
    m
```

Pattern: motive, base, step, input

### Q23: What's boolElim for?

**A**: **Case analysis** on booleans:

```
boolElim : Π(C:Bool → Type).
           C true →   -- True case
           C false →  -- False case
           Π(b:Bool). C b
```

Example - boolean NOT:
```
not : Bool → Bool
not = \(b:Bool).
  boolElim
    (\(_:Bool). Bool)    -- Always returns Bool
    false                -- not true = false
    true                 -- not false = true
    b
```

### Q24: How does vecElim work?

**A**: Recursion on vectors with length tracking:

```
vecElim : Π(A:Type).
          Π(C:Π(n:Nat). Vec A n → Type).
          C 0 (vnil A) →                           -- Nil case
          (Π(n:Nat). Π(x:A). Π(xs:Vec A n).
            C n xs → C (succ n) (vcons A n x xs)) →  -- Cons case
          Π(n:Nat). Π(v:Vec A n). C n v
```

Example - vector sum:
```
vsum : Π(n:Nat). Vec Nat n → Nat
vsum = \(n:Nat). \(v:Vec Nat n).
  vecElim Nat
    (\(k:Nat). \(vec:Vec Nat k). Nat)  -- Result type
    0                                   -- Empty sum
    (\(k:Nat). \(x:Nat). \(xs:Vec Nat k). \(rec:Nat). x + rec)
    n v
```

### Q25: What's emptyElim and why is it useful?

**A**: **Ex falso quodlibet** - from false, derive anything:

```
emptyElim : Π(C:Type). Empty → C
```

**Empty** has NO constructors, so this is vacuously true!

Uses:
1. **Proving by contradiction**: If Empty, then anything
2. **Absurd patterns**: Show case is impossible
3. **Negation**: `¬A = A → Empty`

Example:
```
not_zero_is_succ : Π(n:Nat). ¬(0 = succ n)
not_zero_is_succ = \(n:Nat). \(p:Eq Nat 0 (succ n)).
  -- Derive contradiction, use emptyElim
  emptyElim ... (... p ...)
```

---

## Comparison Questions

### Q26: Chapter 7 vs Chapter 8?

**A**:

| Feature | Chapter 7 | Chapter 8 |
|---------|-----------|-----------|
| **Consistency** | Inconsistent (Type:Type) | Consistent (hierarchy) |
| **Equality** | Definitional only | Propositional (Eq) |
| **Proofs** | Limited | Full theorem proving |
| **Induction** | Basic | Complete (J, eliminators) |
| **Real use** | Learning only | Real proofs! |

**Chapter 7**: Simplified for learning
**Chapter 8**: Production-ready dependent types!

### Q27: How close is this to Agda/Coq/Lean?

**A**: **Very close!** Chapter 8 is essentially:

- **Agda**: Almost identical (intensional type theory)
- **Coq**: CIC (Calculus of Inductive Constructions) - similar structure
- **Lean**: Very similar, with optimizations
- **Idris**: Similar, more practical focus

Differences:
- Real systems have MUCH more:
  - Pattern matching syntax
  - Tactic languages
  - Standard libraries
  - Optimizations

**But core ideas**: Same as Chapter 8!

### Q28: Can I encode all of mathematics?

**A**: **Almost!** You can encode:

✓ Natural numbers, integers, rationals, reals
✓ Sets, relations, functions  
✓ Group theory, category theory
✓ Analysis, topology (with effort)
✓ Most of constructive mathematics

✗ Classical logic (without axioms)
✗ Non-constructive choice (without axioms)

Can ADD classical axioms if needed, but loses computational content.

### Q29: What about undecidability?

**A**: **Type checking** is still decidable!

- Normalization terminates (strong normalization)
- Type checking algorithm always finishes
- **BUT**: Proofs can be hard to construct

You can express undecidable predicates, but type checker won't find proofs automatically!

---

## Practical Proving

### Q30: How do I prove n + 0 = n?

**A**: Induction on n:

```
plus_zero : Π(n:Nat). Eq Nat (n + 0) n
plus_zero = \(n:Nat).
  natElim
    (\(k:Nat). Eq Nat (k + 0) k)    -- Motive
    (refl 0)                        -- Base: 0 + 0 = 0
    (\(k:Nat). \(IH:Eq Nat (k + 0) k).
      -- Step: (k+1) + 0 = k+1
      -- Given IH: k + 0 = k
      -- Need: (k+1) + 0 = k+1
      ... use J to rewrite with IH ...)
    n
```

Key: Use J to rewrite with inductive hypothesis!

### Q31: How do I prove transitivity of equality?

**A**: Using J:

```
trans : Π(A:Type). Π(x y z:A). Eq A x y → Eq A y z → Eq A x z
trans = \(A:Type). \(x y z:A). \(p:Eq A x y). \(q:Eq A y z).
  J A
    (\(x':A). \(y':A). \(p':Eq A x' y'). Π(z':A). Eq A y' z' → Eq A x' z')
    (\(w:A). \(z':A). \(q':Eq A w z'). q')
    x y p z q
```

Template: Set up motive, prove for refl, apply J!

### Q32: What's a good proof strategy?

**A**:

1. **State what you're proving** (the type)
2. **Identify the structure** (Nat? Vec? Equality?)
3. **Choose eliminator** (natElim, vecElim, J)
4. **Prove base case** (usually trivial)
5. **Prove inductive step** (use IH!)
6. **Use J for equality rewrites**

**Pro tip**: Start simple, build up complexity!

### Q33: How do I debug proof errors?

**A**: Strategies:

1. **Type check each piece**:
   ```
   :type base_case
   :type inductive_step
   ```

2. **Simplify the goal**:
   ```
   First prove: 0 + n = n
   Then prove: m + 0 = m
   Then prove: (m + n) + p = m + (n + p)
   ```

3. **Use holes** (if available):
   ```
   natElim ... ? ...    -- Fill in ? later
   ```

4. **Check normalization**:
   ```
   :normalize (3 + 0)   -- Should be 3
   ```

5. **Read error messages carefully**:
   - What type is expected?
   - What type did you provide?
   - Where do they differ?

---

## "I'm Stuck" Scenarios

### Q34: "My proof doesn't type check and I don't know why"

**A**: Checklist:

1. **Motive correct?** Does it return right type for each case?
2. **Base case type matches?** Check against motive
3. **Inductive step types match?** Check IH usage
4. **Universe levels correct?** Type might be in wrong universe
5. **Equality oriented right?** Maybe you need sym
6. **Normalization happening?** Types might not be reducing

**Debug**: Comment out parts, check pieces individually!

### Q35: "How do I use the inductive hypothesis?"

**A**: **Pattern**: IH is the result of recursive call

```
natElim
  C                  -- Motive
  base              -- C 0
  (\(k:Nat). \(IH:C k). ...)    -- IH is "result for k"
                       ↑ Use IH here to build C (k+1)
  n
```

Example:
```
Proving: Π(n:Nat). 2 * n = n + n

IH: 2 * k = k + k     (for predecessor k)
Goal: 2 * (k+1) = (k+1) + (k+1)

Compute:
  2 * (k+1) = 2*k + 2      (by def of *)
            = (k+k) + 2    (by IH!)
            = (k+1) + (k+1) (by algebra)
```

### Q36: "I need to rewrite using an equality"

**A**: Use J! Template:

```
Given: p : Eq A x y
Want: Change x to y in some type

J A
  (\(a:A). \(b:A). \(eq:Eq A a b). [Your goal with b])
  ([Proof for x])
  x y p
```

Example:
```
Given: p : Eq Nat m n
Have: Vec Nat m
Want: Vec Nat n

Use: transport A B p : A → B
where transport uses J internally!
```

### Q37: "Vec operations are too complex!"

**A**: Break them down:

**vappend** - append vectors:
1. Recurse on first vector
2. Base: vnil ++ ys = ys
3. Step: (x :: xs) ++ ys = x :: (xs ++ ys)

**vmap** - map over vector:
1. Recurse on vector  
2. Base: map f vnil = vnil
3. Step: map f (x :: xs) = f x :: map f xs

**Key**: Length tracking happens automatically if you use eliminators correctly!

### Q38: "How do I prove something is impossible?"

**A**: Prove it implies Empty, use emptyElim!

```
not_eq : ¬(Eq Nat 0 1)
not_eq = \(p:Eq Nat 0 1).
  -- Show p leads to contradiction
  -- Use J to analyze p
  -- Derive Empty
  ... (emptyElim at the end)
```

**Technique**: Show constructors don't match, use injectivity!

---

## Advanced Topics

### Q39: What's the computational content of proofs?

**A**: **Curry-Howard**: Proofs ARE programs!

```
Proof of Π(n:Nat). Eq Nat (n + 0) n
   ↓
PROGRAM that computes equality proof

Can EXTRACT and RUN the program!
```

Example:
```
sort_correct : Π(xs:List A). sorted (sort xs)

Extract:
- sort : List A → List A
- Proof that result is sorted (erasable at runtime)

Run sort, discard proof!
```

### Q40: What are "large eliminations" used for?

**A**: Computing **types** from data:

```
boolElim (λ(b:Bool). if b then Nat else Bool) ...
          ↑ Returns TYPE based on b!
```

Uses:
- Type-level computation
- Dependent types in full
- Generic programming at type level

Restriction in some systems because can break consistency!

### Q41: Can I define my own equality type?

**A**: **No need!** Eq is THE equality type.

But you can define:
- **Decidable equality**: `Dec (Eq A x y) = (Eq A x y) + ¬(Eq A x y)`
- **Setoid equality**: Custom equivalence relations
- **Observational equality**: Extensional variants

Eq is the **propositional equality** built-in.

### Q42: What's "proof irrelevance"?

**A**: All proofs of same proposition are equal:

```
Proof Irrelevance: Π(p q:Eq A x y). Eq (Eq A x y) p q
```

**In this chapter**: NOT necessarily true (intensional)
**In some systems**: Can be added as axiom
**In HoTT**: Rejected!

Affects definitional vs propositional equality.

---

## Quick Reference: Proof Strategies

| Goal | Eliminator | Strategy |
|------|-----------|----------|
| Property of Nat | natElim | Induction on n |
| Property of Bool | boolElim | Case analysis |
| Property of Vec | vecElim | Induction on vector |
| Property of equality | J | Prove for refl |
| Contradiction | emptyElim | Derive Empty |
| Equality rewrite | J or cong | Use J to substitute |

---

## Further Reading

- **The HoTT Book**: Homotopy Type Theory (free online!)
- **Certified Programming with Dependent Types** (CPDT): Practical Coq
- **Programming in Martin-Löf's Type Theory**: Classic introduction
- **Type Theory and Formal Proof**: Comprehensive textbook

**Practice platforms**:
- Agda tutorial
- Coq's Software Foundations
- Lean's theorem proving tutorial

---

*"With universe hierarchy and propositional equality, dependent type theory becomes a foundation for ALL of mathematics!" - The power of Chapter 8*

**You've reached the summit! 🏔️ From here, you can verify programs, prove theorems, and explore the deepest connections between logic, computation, and mathematics!**
