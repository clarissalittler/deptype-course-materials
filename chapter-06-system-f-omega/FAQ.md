# Chapter 6: System F-omega (Higher-Kinded Types) - Frequently Asked Questions

## Table of Contents

1. [Conceptual Questions](#conceptual-questions)
2. [Kinds](#kinds)
3. [Type Operators](#type-operators)
4. [Higher-Kinded Polymorphism](#higher-kinded-polymorphism)
5. [Practical Applications](#practical-applications)
6. [Practical "I'm Stuck" Scenarios](#practical-im-stuck-scenarios)

---

## Conceptual Questions

### Q1: What's the difference between System F and System F-ω?

**A**:

| Feature | System F | System F-ω |
|---------|----------|------------|
| **Kind system** | Only `*` (implicit) | Full kinds: `*`, `* → *`, etc. |
| **Type operators** | No | Yes: `λα:κ. τ` |
| **Higher-kinded types** | No | Yes: `∀α:*→*. ...` |
| **Type-level computation** | No | Yes |

System F-ω adds "types of types" (kinds) and computation at the type level.

### Q2: Why do we need kinds?

**A**: To classify type constructors by their "arity":
```
Int    : *           -- A complete type
List   : * → *       -- Takes one type, returns a type
Map    : * → * → *   -- Takes two types, returns a type
Monad  : (* → *) → * -- Takes a type constructor!
```

Without kinds, we couldn't distinguish `List` (needs a parameter) from `Int` (complete type).

### Q3: What's a "type operator"?

**A**: A function at the type level:
```
Pair = λα:*. λβ:*. α × β

Pair Nat Bool = Nat × Bool
```

Just like term-level lambdas, but for types!

### Q4: What can System F-ω express that System F can't?

**A**:
1. **Type constructors as parameters**: `∀F:*→*. F Nat → F Bool`
2. **Functor/Monad interfaces**: Abstract over type constructors
3. **Type-level computation**: Build types programmatically
4. **Generic data structure operations**: Map, fold over any container

---

## Kinds

### Q5: What is a kind?

**A**: The "type of a type". Just as types classify terms:
```
5 : Nat
true : Bool
```

Kinds classify types:
```
Nat  : *
List : * → *
(→)  : * → * → *
```

### Q6: What's the base kind `*`?

**A**: `*` (pronounced "star" or "type") is the kind of ordinary types:
```
Nat : *
Bool : *
Nat → Bool : *
∀α:*. α → α : *
```

These are "complete" types that can classify terms.

### Q7: What does `* → *` mean?

**A**: A type that needs one type to become complete:
```
List : * → *

List Nat : *    -- Now complete!
List Bool : *   -- Also complete!
```

`List` alone is NOT a type (can't have `x : List`).
`List Nat` IS a type (can have `x : List Nat`).

### Q8: Can I have higher kinds like `(* → *) → *`?

**A**: Yes! These are types that take type constructors:
```
Fix : (* → *) → *
-- Takes a type constructor like List, returns a type
```

Or kinds with multiple arrows:
```
Bifunctor : * → * → *
Transform : (* → *) → (* → *)
```

### Q9: How do I know what kind something has?

**A**: Count the type parameters:
- No parameters → `*`
- One parameter → `* → *`
- Two parameters → `* → * → *`
- Takes a `* → *` and produces `*` → `(* → *) → *`

### Q10: What's kind polymorphism?

**A**: Abstracting over kinds themselves:
```
∀κ. ∀α:κ. ...
```

System F-ω typically doesn't have this - you need **System F-ω₂** or dependent types for full kind polymorphism.

---

## Type Operators

### Q11: How do I write a type-level lambda?

**A**: Same syntax, but at the type level:
```
λα:*. α × α      -- Takes type, returns product with itself
λα:*. List α     -- Takes type, wraps in List
λα:*. α → α      -- Takes type, returns function type
```

### Q12: How do type operators reduce?

**A**: Same as term-level beta reduction:
```
(λα:*. α × α) Nat
→ Nat × Nat
```

Types are "computed" before type checking.

### Q13: Can type operators be recursive?

**A**: Not directly in basic F-ω. But you can encode fixed points:
```
Fix = λF:*→*. ∀α:*. (F α → α) → α
```

This is how you encode recursive types like lists.

### Q14: What's the difference between `Pair` and `(×)`?

**A**:
```
-- Pair as type operator
Pair = λα:*. λβ:*. α × β
Pair : * → * → *

-- × as built-in type constructor
(×) : * → * → *
Nat × Bool : *
```

Pair is defined in terms of ×, but behaves identically.

---

## Higher-Kinded Polymorphism

### Q15: What is higher-kinded polymorphism?

**A**: Abstracting over type constructors:
```
∀F:*→*. F Nat → F Bool
```

This type says: "For ANY type constructor F, a function from F applied to Nat to F applied to Bool."

Examples of F: List, Maybe, Tree, ...

### Q16: How do I use a higher-kinded type parameter?

**A**: Apply it to other types:
```
Λ(F : * → *). λ(x : F Nat). ...
               ↑ F is applied to Nat
```

You can only apply F to types of the right kind.

### Q17: What's a Functor in F-ω?

**A**: A type constructor with a map operation:
```
FunctorOps = λF:*→*. ∀α:*. ∀β:*. (α → β) → F α → F β
```

This says: For type constructor F, we can lift any function `α → β` to work on `F α → F β`.

### Q18: What's a Monad in F-ω?

**A**:
```
MonadOps = λM:*→*.
  { return : ∀α:*. α → M α
  , bind   : ∀α:*. ∀β:*. M α → (α → M β) → M β
  }
```

A type constructor M with return and bind operations.

### Q19: How does this relate to Haskell's typeclasses?

**A**: Very closely! Haskell's:
```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
```

Is essentially:
```
Functor : (* → *) → *
Functor = λF:*→*. ∀α:*. ∀β:*. (α → β) → F α → F β
```

Haskell adds the convenience of implicit dictionary passing.

---

## Practical Applications

### Q20: Why are higher-kinded types useful?

**A**: They enable **abstraction over containers**:
- Write ONE map function that works for List, Tree, Maybe, ...
- Write ONE traversal that works for any Functor
- Define interfaces (Functor, Monad) once, implement many times

### Q21: Can I encode List in F-ω?

**A**: Yes, using Church encoding:
```
List = λα:*. ∀β:*. (α → β → β) → β → β

nil : ∀α:*. List α
nil = Λα:*. Λβ:*. λc:α→β→β. λn:β. n

cons : ∀α:*. α → List α → List α
cons = Λα:*. λh:α. λt:List α. Λβ:*. λc:α→β→β. λn:β. c h (t [β] c n)
```

### Q22: Can I encode Trees in F-ω?

**A**: Yes!
```
Tree = λα:*. ∀β:*. β → (α → β → β → β) → β

leaf : ∀α:*. Tree α
node : ∀α:*. α → Tree α → Tree α → Tree α
```

### Q23: What about recursive types?

**A**: F-ω doesn't have built-in recursive types, but you can encode them with:
```
μ = λF:*→*. ∀α:*. (F α → α) → α
```

This is the "least fixed point" of F.

---

## Practical "I'm Stuck" Scenarios

### Q24: "Kind mismatch: expected * but got * → *"

**A**: You're using a type constructor where a complete type is expected:
```
-- Wrong:
λx:List. ...    -- List needs a type argument!

-- Right:
λx:List Nat. ...    -- List Nat is complete
```

### Q25: "Cannot apply type of kind * to argument"

**A**: You're trying to apply a complete type like a constructor:
```
-- Wrong:
Nat Bool    -- Nat : *, can't apply to Bool

-- Right:
List Bool   -- List : * → *, can apply to Bool
```

### Q26: "Type operator doesn't reduce"

**A**: Make sure you're applying to the right kinds:
```
Pair = λα:*. λβ:*. α × β

-- Wrong:
Pair List    -- List : * → *, but Pair expects *

-- Right:
Pair Nat Bool    -- Both : *
```

### Q27: "How do I write a function polymorphic in a type constructor?"

**A**: Use Λ with a higher kind:
```
Λ(F : * → *). λ(x : F Nat). ...
```

The kind annotation `* → *` is crucial!

### Q28: "What's the kind of my type operator?"

**A**: Build from structure:
```
λα:*. λβ:*. α → β
```

1. `λα:*.` takes a type: `* → ...`
2. `λβ:*.` takes another: `* → * → ...`
3. `α → β : *` (complete type)

Result: `* → * → *`

### Q29: "How do I abstract over both the container and element type?"

**A**: Use two type parameters:
```
Λ(F : * → *). Λ(α : *). λ(x : F α). ...
```

This abstracts over:
- F: the container (List, Tree, etc.)
- α: the element type (Nat, Bool, etc.)

---

## Quick Reference

### Kind Syntax
```
κ ::= *           -- Base kind (proper types)
    | κ₁ → κ₂     -- Type operator kind
```

### Type Syntax (additions)
```
τ ::= ...
    | λα:κ. τ     -- Type operator
    | τ₁ τ₂       -- Type application
```

### Typing Rules
```
Γ, α:κ₁ ⊢ τ : κ₂
───────────────────── (K-TAbs)
Γ ⊢ λα:κ₁. τ : κ₁ → κ₂

Γ ⊢ τ₁ : κ₁ → κ₂    Γ ⊢ τ₂ : κ₁
───────────────────────────────── (K-TApp)
Γ ⊢ τ₁ τ₂ : κ₂
```

### Common Kinds
```
Nat, Bool, String    : *
List, Maybe, IO      : * → *
Either, (,), (→)     : * → * → *
StateT, ReaderT      : * → (* → *) → * → *
```

---

## Further Reading

- **Girard (1972)**: Original System F-ω in thesis
- **Pierce TAPL Chapter 29-30**: Higher-order polymorphism
- **Harper PFPL Chapters 20-21**: Higher kinds
- **Barendregt (1992)**: Lambda Calculi with Types (Handbook)

**Remember**: System F-ω gives you the full power of abstraction at the type level. If you can abstract over values (λ) and types (Λ), why not abstract over type constructors too?
