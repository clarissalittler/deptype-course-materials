# Chapter 5: System F (Polymorphic Lambda Calculus) - Frequently Asked Questions

## Table of Contents

1. [Conceptual Questions](#conceptual-questions)
2. [Type Abstraction and Application](#type-abstraction-and-application)
3. [Universal Types](#universal-types)
4. [Church Encodings](#church-encodings)
5. [Parametricity](#parametricity)
6. [Undecidability](#undecidability)
7. [Practical "I'm Stuck" Scenarios](#practical-im-stuck-scenarios)

---

## Conceptual Questions

### Q1: What's the difference between System F and Hindley-Milner?

**A**:

| Feature | Hindley-Milner (Ch4) | System F (Ch5) |
|---------|---------------------|----------------|
| **Type annotations** | Not needed | Required on Λ |
| **Where polymorphism** | Only at `let` | Anywhere |
| **Type inference** | Decidable | Undecidable |
| **Polymorphic arguments** | No | Yes |
| **Impredicativity** | No | Yes |

System F is more expressive but requires more annotations.

### Q2: Why is it called "System F"?

**A**: Jean-Yves Girard named it in his 1972 thesis. The "F" likely refers to "Functional" or is simply a letter choice. It's also called the **polymorphic lambda calculus** or **second-order lambda calculus**.

John Reynolds independently discovered the same system in 1974!

### Q3: What's "explicit polymorphism"?

**A**: You explicitly write type abstractions and applications:
```
-- Identity function
id = Λα. λx:α. x

-- Using it at specific types
id [Nat] 5        -- apply to Nat
id [Bool] true    -- apply to Bool
```

Compare to Hindley-Milner where this is implicit.

### Q4: What can System F express that simpler systems can't?

**A**:
1. **Polymorphic arguments**: Functions that take polymorphic functions
2. **Church encodings**: All data types as functions
3. **Impredicative types**: Types quantifying over themselves
4. **Higher-rank types**: `∀` nested in function types

---

## Type Abstraction and Application

### Q5: What is type abstraction (Λ)?

**A**: Like lambda for types. Creates a function from types to terms:
```
Λα. λx:α. x
```
Read as: "For any type α, take a value x of type α, return x."

### Q6: What is type application ([τ])?

**A**: Applying a polymorphic term to a specific type:
```
(Λα. λx:α. x) [Nat]
= λx:Nat. x
```
The type parameter α is replaced with Nat.

### Q7: How do I read `Λα. λx:α. α → α`?

**A**: Step by step:
- `Λα.`: "For any type α..."
- `λx:α.`: "...take a value x of type α..."
- Body has type `α → α`

Full type: `∀α. α → (α → α)`

### Q8: What's the evaluation order for type applications?

**A**: Type applications are **compile-time** operations:
```
(Λα. λx:α. x) [Nat] 5
→ (λx:Nat. x) 5    -- Type application first
→ 5                 -- Then value application
```

At runtime, types are "erased" (type erasure).

---

## Universal Types

### Q9: What is a universal type (∀)?

**A**: A type that works for ALL types:
```
∀α. α → α
```
Means: "For any type α, a function from α to α."

This is the type of the polymorphic identity function.

### Q10: What's the difference between `∀α. α → α` and `α → α`?

**A**:
- `∀α. α → α`: A single function that works for ANY type
- `α → α`: A function for one SPECIFIC (but unknown) type α

The ∀ lets you use the SAME function at different types.

### Q11: Can I have multiple type parameters?

**A**: Yes!
```
Λα. Λβ. λx:α. λy:β. x
: ∀α. ∀β. α → β → α
```
This is the K combinator, polymorphically typed.

### Q12: What's "impredicativity"?

**A**: Types can quantify over themselves!
```
∀α. α → α
```
This ∀ ranges over ALL types, including `∀α. α → α` itself!

This enables things like:
```
id [∀α. α → α] id    -- Apply id to its own type
```

Impredicativity makes type inference undecidable.

---

## Church Encodings

### Q13: What are Church encodings in System F?

**A**: Represent data types as polymorphic functions:

**Booleans**:
```
Bool = ∀α. α → α → α
true  = Λα. λt:α. λf:α. t
false = Λα. λt:α. λf:α. f
```

**Natural numbers**:
```
Nat = ∀α. (α → α) → α → α
zero = Λα. λs:α→α. λz:α. z
succ = λn:Nat. Λα. λs:α→α. λz:α. s (n [α] s z)
```

### Q14: Why use Church encodings?

**A**: They show that System F can represent ANY data type without built-in primitives!

**Theoretical importance**: System F is computationally complete using only:
- Type abstraction (Λ)
- Type application ([τ])
- Lambda abstraction (λ)
- Application

### Q15: How do I use Church booleans?

**A**: They ARE if-then-else!
```
if b then t else f  =  b [τ] t f
```

Example:
```
true [Nat] 1 0  = 1
false [Nat] 1 0 = 0
```

### Q16: How do I add Church numerals?

**A**:
```
add = λm:Nat. λn:Nat. Λα. λs:α→α. λz:α. m [α] s (n [α] s z)
```

Intuition: m applies s m times, n applies s n more times.

---

## Parametricity

### Q17: What is parametricity?

**A**: A function with type `∀α. α → α` MUST be the identity!

Why? It works for ANY type, so it can't:
- Examine the value (unknown type)
- Produce a different value (unknown type)
- Call any functions on it (unknown type)

It can ONLY return what it was given.

### Q18: What are "free theorems"?

**A**: Theorems derived just from types! From `f : ∀α. α → α`:
```
For any g : A → B and x : A:
  g (f [A] x) = f [B] (g x)
```

The function `f` "commutes" with any function `g`!

### Q19: What can I deduce from `∀α. α → α → α`?

**A**: The function must return one of its arguments:
```
f : ∀α. α → α → α
```

So f is either:
- `Λα. λx:α. λy:α. x` (return first), or
- `Λα. λx:α. λy:α. y` (return second)

Only TWO possible implementations!

### Q20: Why is parametricity useful?

**A**:
1. **Reasoning**: Derive properties from types alone
2. **Optimization**: Compiler can specialize polymorphic code
3. **Abstraction**: Guaranteed encapsulation
4. **Security**: Data hiding without runtime checks

---

## Undecidability

### Q21: Why is System F type inference undecidable?

**A**: Wells (1999) proved it reduces to an undecidable problem.

**Key reasons**:
- Impredicativity: Types can quantify over themselves
- Higher-rank types: ∀ can appear anywhere
- No principal types: Multiple incomparable valid types

### Q22: If inference is undecidable, how do we use System F?

**A**: We require **annotations**:
```
Λα. λx:α. x    -- Must write the Λα explicitly
```

The type CHECKING is decidable - just inference isn't.

### Q23: What subset of System F has decidable inference?

**A**: Hindley-Milner! It restricts:
- ∀ only at outermost level (prenex form)
- ∀ only on let-bindings
- No impredicativity

This gives you automatic inference with most of the power.

---

## Practical "I'm Stuck" Scenarios

### Q24: "Expected ∀α. τ but got τ'"

**A**: You need a type abstraction:
```
-- Wrong:
λx:α. x    -- α is free, not bound

-- Right:
Λα. λx:α. x    -- α is bound by Λ
```

### Q25: "Can't apply term to type"

**A**: Only polymorphic terms can receive type arguments:
```
-- Wrong:
5 [Nat]    -- 5 is not polymorphic

-- Right:
(Λα. λx:α. x) [Nat]    -- id IS polymorphic
```

### Q26: "Type variable not in scope"

**A**: Introduce it with Λ:
```
-- Wrong:
λx:α. x    -- Where does α come from?

-- Right:
Λα. λx:α. x    -- α is introduced here
```

### Q27: "How do I instantiate a polymorphic function?"

**A**: Use type application:
```
id : ∀α. α → α

id [Nat] 5      -- id instantiated to Nat
id [Bool] true  -- id instantiated to Bool
```

### Q28: "My Church encoding doesn't type check"

**A**: Common issues:
1. **Missing type abstraction**: Λα. is required
2. **Wrong order**: Type args before value args
3. **Type annotation**: Make sure function types match

Debug by checking each piece:
```
zero : Nat
zero = Λα. λs:α→α. λz:α. z
      ^    ^        ^
      Type param, then value params
```

### Q29: "What's the type of my function?"

**A**: Build it from the structure:
```
Λα. Λβ. λf:α→β. λx:α. f x
```

1. `Λα.` introduces type param α: `∀α. ...`
2. `Λβ.` introduces type param β: `∀α. ∀β. ...`
3. `λf:α→β.` takes function: `∀α. ∀β. (α → β) → ...`
4. `λx:α.` takes value: `∀α. ∀β. (α → β) → α → ...`
5. `f x` has type β: `∀α. ∀β. (α → β) → α → β`

---

## Quick Reference

### Typing Rules

```
Γ, α type ⊢ t : τ
─────────────────────── (T-TAbs)
Γ ⊢ Λα. t : ∀α. τ

Γ ⊢ t : ∀α. τ
─────────────────── (T-TApp)
Γ ⊢ t [σ] : τ[α := σ]
```

### Key Types

```
Id      = ∀α. α → α
Bool    = ∀α. α → α → α
Nat     = ∀α. (α → α) → α → α
List α  = ∀β. (α → β → β) → β → β
```

---

## Further Reading

- **Girard (1972)**: Original System F thesis
- **Reynolds (1974)**: "Towards a theory of type structure"
- **Reynolds (1983)**: "Types, Abstraction and Parametric Polymorphism"
- **Wadler (1989)**: "Theorems for free!"
- **Wells (1999)**: Undecidability proof

**Remember**: System F is the most expressive system with decidable type CHECKING. It's the foundation for understanding parametric polymorphism!
