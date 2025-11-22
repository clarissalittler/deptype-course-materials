# Chapter 7: Dependent Types - Frequently Asked Questions

## Table of Contents

1. [Conceptual Foundation](#conceptual-foundation)
2. [Pi Types Questions](#pi-types-questions)
3. [Sigma Types Questions](#sigma-types-questions)
4. [Type-in-Type Questions](#type-in-type-questions)
5. [Comparison Questions](#comparison-questions)
6. [Practical Implementation](#practical-implementation)
7. ["I'm Stuck" Scenarios](#im-stuck-scenarios)
8. [Advanced Topics](#advanced-topics)

---

## Conceptual Foundation

### Q1: What ARE dependent types (in simple terms)?

**A**: Types that can depend on VALUES!

Non-dependent (Chapter 2-6):
```
Nat → Nat        "Function from Nat to Nat"
```

Dependent (Chapter 7):
```
Π(n:Nat). Vec Nat n    "Function that takes n, returns vector of length n"
                                                        ↑ TYPE depends on VALUE n!
```

The result type CHANGES based on the input value!

### Q2: Why are terms and types unified?

**A**: In dependent types, types can compute, so they need the full power of terms:

```
\(n:Nat). Vec Nat n : Nat → Type
```

This is a FUNCTION that returns a TYPE! To make this work, terms and types must use the same language.

**Consequence**: `Type` is itself a term that has a type!

### Q3: What's the big deal about dependent types?

**A**: **Precision in types!** You can express properties:

```
sort : Π(n:Nat). Vec Int n → Vec Int n
```
Type says: "Sorting preserves length!"

```
safeHead : Π(n:Nat). Vec A (succ n) → A
```
Type says: "Only works on non-empty vectors!"

Types become **specifications** that the compiler checks!

### Q4: What's the Curry-Howard correspondence here?

**A**: Even more powerful than before!

| Logic | Types |
|-------|-------|
| ∀x. P(x) | Π(x:A). B |
| ∃x. P(x) | Σ(x:A). B |
| P → Q | A → B (special case of Π) |
| P ∧ Q | A * B (special case of Σ) |

**Programs = Proofs**, **Types = Propositions**

Example:
```
\(A:Type). \(x:A). x : Π(A:Type). A → A
```
This is a PROOF that "for all types A, A implies A"!

### Q5: How is this different from System F?

**A**:

**System F**: Polymorphism over types
```
/\A. \x:A. x     "For all TYPES A..."
```

**Dependent Types**: Functions over types AND values
```
\(A:Type). \(x:A). x     "Function that takes type A and value x..."
\(n:Nat). Vec Nat n      "Function that takes value n and returns TYPE"
```

Dependent types are MORE general - they include System F as a special case!

---

## Pi Types Questions

### Q6: What exactly is a Pi type Π(x:A). B?

**A**: A **dependent function type** where:
- Input has type A
- Output has type B
- B can MENTION x (depend on the input!)

Example:
```
Π(n:Nat). Vec Nat n
  ↑        ↑
  input   output type (using n!)
```

If x doesn't appear in B, it's just a regular function type: `A → B`

### Q7: When do I use Π vs →?

**A**:

Use `→` when result type doesn't depend on input:
```
Nat → Nat           "Always returns Nat"
Bool → Type         "Always returns a Type"
```

Use `Π` when result type DOES depend on input:
```
Π(n:Nat). Vec Nat n          "Returns different type for each n"
Π(b:Bool). if b then Nat else Bool    "Type depends on b!"
```

**Syntactic sugar**: `A → B` is shorthand for `Π(x:A). B` when x ∉ B

### Q8: How do I read Π(n:Nat). Π(m:Nat). Vec Nat (n + m)?

**A**: Step by step:

```
Π(n:Nat). Π(m:Nat). Vec Nat (n + m)
  ↑        ↑         ↑
  Input 1  Input 2   Result type (depends on both!)
```

In English: "Function that takes two Nats n and m, returns vector of length n+m"

**Curried form**: Each Π binds one argument at a time.

### Q9: Can I have nested Pi types?

**A**: Absolutely! Example:

```
Π(A:Type). Π(B:Type). Π(f:A → B). Π(x:A). B
```

This is the type of function application:
1. Take type A
2. Take type B
3. Take function f : A → B
4. Take value x : A
5. Return B (by applying f to x)

**Each level can depend on previous levels!**

### Q10: What's a "dependent product"?

**A**: Another name for Pi types (Π)! Called "product" because:
- Like Cartesian product: ∏ᵢ Aᵢ
- For each value x:A, we get a type B(x)
- "Product" of all these types

Don't confuse with **pair types** (those are Sigma types)!

---

## Sigma Types Questions

### Q11: What is a Sigma type Σ(x:A). B?

**A**: A **dependent pair** where:
- First component has type A
- Second component has type B
- B can MENTION the first component!

Example:
```
Σ(n:Nat). Vec Nat n
```
Pair of: (a number n, a vector of length n)

Second component's TYPE depends on first component's VALUE!

### Q12: Σ vs regular pairs (A * B)?

**A**:

**Regular pair** (non-dependent):
```
Nat * Bool         "Pair of Nat and Bool"
(42, true)         Both types known independently
```

**Dependent pair** (Sigma):
```
Σ(n:Nat). Vec Nat n      "Pair where second type depends on first value"
(3, [1, 2, 3])           Second component is vector of length 3
(5, [1,2,3,4,5])         Second component is vector of length 5
```

**Sugar**: `A * B` is shorthand for `Σ(x:A). B` when x ∉ B

### Q13: How do Sigma types relate to existential types?

**A**: They're intimately related!

**Existential type**:
```
∃A. (A * (A → String))
"There exists a type A, with a value of type A and a function A → String"
```

**Sigma encoding**:
```
Σ(A:Type). A * (A → String)
"Pair of: a type A, and a pair (value, function)"
```

Sigma types can encode existentials!

Example use: Abstract data types
```
Σ(State:Type). (State * (State → State → State) * ...)
"Hidden state type with operations"
```

### Q14: What does "dependent" really mean?

**A**: The TYPE of later components depends on VALUE of earlier ones:

```
Σ(isValid:Bool). if isValid then Nat else Unit
                        ↑ TYPE depends on VALUE of isValid!

If first component is true: second is Nat
If first component is false: second is Unit
```

This is IMPOSSIBLE in non-dependent systems!

---

## Type-in-Type Questions

### Q15: What is Type-in-Type and why is it a problem?

**A**: In Chapter 7: `Type : Type`

This seems convenient but allows **Girard's paradox** - you can prove false!

Like Russell's paradox in set theory:
```
R = {x | x ∉ x}     "Set of all sets that don't contain themselves"
R ∈ R?              Contradiction!
```

Similarly, Type-in-Type allows encoding of paradoxes.

**Solution**: Chapter 8's universe hierarchy!

### Q16: Can I still use Chapter 7 for real work?

**A**: **For learning**: Yes! Perfectly fine to understand dependent types.

**For proofs**: NO! You could prove false, making the system unsound.

**In practice**: Use Chapter 8 (or Agda/Coq/Lean) which have universe hierarchies.

**Chapter 7 = simplified but unsound**
**Chapter 8 = complex but sound**

### Q17: How does Type-in-Type make things inconsistent?

**A**: You can encode "set of all sets not containing themselves":

```
U = Π(A:Type). (A → Type) → Type
```

With Type:Type, this allows circular constructions that prove false.

**Famous proof**: Hurkens' paradox (too complex for FAQ, but provable in Type-in-Type!)

### Q18: Why not just ignore the paradox?

**A**: If you can prove `False`, you can prove ANYTHING:

```
false_implies_anything : False → Π(A:Type). A
```

The whole system becomes meaningless for verification!

This is why real proof assistants (Agda, Coq, Lean) all use universe hierarchies.

---

## Comparison Questions

### Q19: Dependent Types vs System F?

**A**:

| Feature | System F (Ch5) | Dependent Types (Ch7) |
|---------|---------------|----------------------|
| Types depend on | Types | Values AND types |
| Terms and types | Separate | Unified |
| Polymorphism | ∀A. ... | Π(A:Type). ... |
| Type-level functions | Limited | Full computation |
| Curry-Howard | Propositional logic | Predicate logic |

Dependent types are STRICTLY more powerful!

### Q20: Can all System F terms be expressed in dependent types?

**A**: YES! System F embedable in dependent types:

```
System F:  ∀A. A → A
Dependent: Π(A:Type). A → A

System F:  ∀A. ∀B. (A → B) → A → B
Dependent: Π(A:Type). Π(B:Type). (A → B) → A → B
```

Dependent types **generalize** System F!

### Q21: What can dependent types express that System F can't?

**A**:

1. **Length-indexed vectors**:
   ```
   Vec A n      (Can't express in System F!)
   ```

2. **Type-level computation**:
   ```
   \(n:Nat). Vec Nat n : Nat → Type
   ```

3. **Precise specifications**:
   ```
   sorted : Π(n:Nat). Vec Int n → Vec Int n
   ```

4. **Proofs as programs**:
   ```
   plus_comm : Π(n:Nat). Π(m:Nat). n + m = m + n
   ```

---

## Practical Implementation

### Q22: How do I actually write a dependent function?

**A**: Just like normal lambda, but parameters can appear in types:

```
\(n:Nat). \(xs:Vec Nat n). ...
  ↑                ↑
  Value           Type using n!
```

Example - vector replication:
```
replicate : Π(n:Nat). Π(A:Type). A → Vec A n
replicate = \(n:Nat). \(A:Type). \(x:A).
  natElim
    (\(k:Nat). Vec A k)
    (vnil A)
    (\(k:Nat). \(rec:Vec A k). vcons A k x rec)
    n
```

### Q23: How does type checking work with dependent types?

**A**: **Normalization-based**!

To check if two types are equal:
1. Normalize both to normal form
2. Check if syntactically equal (up to α-conversion)

Example:
```
(\(x:Nat). Vec Nat x) 3
  normalizes to
Vec Nat 3

These are equal!
```

This means the type checker must **evaluate** types!

### Q24: What's the evaluation strategy?

**A**: Usually **normalization by evaluation** or **weak head normal form**:

- **Full normalization**: Reduce everything (slow but simple)
- **WHNF**: Reduce just enough to see constructor (faster)

For type checking equality, need full normalization.

Example check:
```
Is (\(x:Nat). x) 3 = 3?
  Normalize left: 3
  Normalize right: 3
  Equal? Yes!
```

### Q25: How do I debug dependent type errors?

**A**: Strategy:

1. **Check normalization**: `:normalize` both sides
   ```
   :normalize (\(x:Nat). Vec Nat x) 3
   ```

2. **Simplify types**: Build up complexity gradually
   ```
   First: \(A:Type). A → A
   Then: \(A:Type). \(n:Nat). A → Vec A n
   ```

3. **Use explicit annotations**: Help the checker
   ```
   (\(xs:Vec Nat 3). ...) : Vec Nat 3 → ...
   ```

4. **Check in REPL**: Verify subterms type correctly
   ```
   :type \(n:Nat). Vec Nat n
   ```

---

## "I'm Stuck" Scenarios

### Q26: "Types seem to normalize differently than I expect"

**A**: Remember evaluation order!

```
(\(f:Nat → Nat). f 3) (\(x:Nat). succ x)
  reduces to
(\(x:Nat). succ x) 3
  reduces to
succ 3
  reduces to
4
```

Use `:step` in REPL to see each reduction.

### Q27: "I get 'Type mismatch after normalization'"

**A**: The types don't match even after reducing:

```
Expected: Vec Nat 3
Got: Vec Nat (1 + 2)

Normalize (1 + 2): if your + is defined right, should get 3
If still doesn't match: check your + definition!
```

Common issue: Type-level computation not reducing properly.

### Q28: "How do I prove two things are equal?"

**A**: In Chapter 7, only **definitional equality** (normalization):

```
succ (succ zero) = 2    ✓ (normalize to same thing)
n + 0 = n               ✗ (can't prove without induction!)
```

For more equality, need Chapter 8's propositional equality (Eq type).

### Q29: "My vector operations won't type check"

**A**: Make sure length tracking is precise:

```
vappend : Π(m:Nat). Π(n:Nat). Vec A m → Vec A n → Vec A (m + n)

If you have:
  xs : Vec A 3
  ys : Vec A 2
  vappend 3 2 xs ys : Vec A (3 + 2)

Type checker must compute 3 + 2 = 5
```

Ensure your arithmetic normalizes correctly!

### Q30: "What's 'universe level mismatch'?" (Might see in implementations)

**A**: Some implementations track universe levels even in Type-in-Type.

```
Type0 : Type1
Type1 : Type2
```

If you mix levels wrong:
```
Bad: (Type1 : Type0)
```

Chapter 8 makes this explicit. In Chapter 7, usually ignore or use Type everywhere.

---

## Advanced Topics

### Q31: Can I define recursive types?

**A**: Not directly in pure dependent type theory!

You need **inductive types** (Chapter 8) or **fixed points**.

In Chapter 7, usually work with primitive types (Nat, Bool) and build from there.

### Q32: What's "large elimination"?

**A**: Eliminating into Type (not just values):

```
boolElim : Π(C:Bool → Type). C true → C false → Π(b:Bool). C b
            ↑ Motive returns Type!
```

Large elimination: allowed in most systems
Small elimination: only return values

Chapter 7: both allowed
Some systems: restrict large elimination for consistency reasons

### Q33: How do dependent types relate to subset types?

**A**: Sigma types can encode subsets!

```
{x:Nat | x > 0}

Encode as:
Σ(x:Nat). (x > 0)
  ↑        ↑ proof that x > 0
  value    

"Pair of Nat and proof it's positive"
```

This is refinement types!

### Q34: Can I have dependent pattern matching?

**A**: Need Chapter 8! Basic Chapter 7 has:
- Non-dependent matching
- Eliminators for induction

Chapter 8 adds:
- Full dependent pattern matching
- Inductive families

### Q35: What's "eta-equality" for dependent types?

**A**: Extensional equality of functions:

**Eta for functions**:
```
f = \(x:A). f x      (when x ∉ f)
```

**Eta for pairs**:
```
p = pair (fst p) (snd p)
```

Chapter 7: Usually has eta-equality
Makes reasoning easier but affects decidability

---

## Quick Troubleshooting Guide

| Problem | Likely Cause | Solution |
|---------|--------------|----------|
| Type mismatch after normalization | Computation not reducing | Check definitions, use :normalize |
| Can't use value in type | Not dependent enough | Use Π instead of → |
| Type-in-Type error | Using Chapter 7 limitations | Move to Chapter 8 or accept limitation |
| Infinite loop in type checking | Circular type dependency | Check for well-foundedness |
| Can't prove equality | Only have definitional equality | Use normalization or move to Chapter 8 |

---

## Further Reading

- **Martin-Löf (1984)**: "Intuitionistic Type Theory" - Foundation of dependent types
- **Coquand & Huet (1988)**: "Calculus of Constructions" - Dependent types + System F
- **Barendregt (1992)**: "Lambda Calculi with Types" - Comprehensive reference
- **ATTAPL Chapter "Dependent Types"**: Practical introduction

**Remember**: Dependent types are a big conceptual leap. Take time to let the ideas sink in!

---

*"In dependent type theory, we don't just compute with values - we compute with types too!" - The essence of dependent types*
