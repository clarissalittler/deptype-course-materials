# Chapter 6: Visual Aids

## Kind Hierarchy

```
                     Terms
                       │
                       │ "have type"
                       ▼
                     Types
                       │
                       │ "have kind"
                       ▼
                     Kinds
                       │
                       │ "have sort" (beyond F-omega)
                       ▼
                      ...

Examples:
  5        : Nat      : *
  true     : Bool     : *
  λx. x    : Nat→Nat  : *
  List     : * → *    : □
  Either   : *→*→*    : □
```

---

## Kind Examples

```
┌─────────────────────────────────────────────────────────────┐
│  TYPE                        KIND                           │
├─────────────────────────────────────────────────────────────┤
│  Nat                         *                              │
│  Bool                        *                              │
│  Nat → Bool                  *                              │
│  List                        * → *                          │
│  List Nat                    *                              │
│  Maybe                       * → *                          │
│  Either                      * → * → *                      │
│  Either Nat                  * → *                          │
│  Either Nat Bool             *                              │
│  Functor                     (* → *) → *                    │
│  Monad                       (* → *) → *                    │
└─────────────────────────────────────────────────────────────┘
```

---

## Type-Level Functions

### Type-Level Identity

```
Id = λα:*. α

     TyLam
    /     \
   α:*     α

Application:
  Id Nat = (λα:*. α) Nat
         = [α ↦ Nat]α
         = Nat
```

### Type-Level Composition

```
Compose = λF:*→*. λG:*→*. λα:*. F (G α)

           TyLam
          /     \
       F:*→*    TyLam
               /     \
            G:*→*    TyLam
                    /     \
                  α:*     TyApp
                         /     \
                        F      TyApp
                              /     \
                             G       α

Application:
  Compose List Maybe Nat
  = List (Maybe Nat)
  = [Nat, Nothing, Just 5, ...]  (values of this type)
```

---

## Kinding Derivations

### For `List Nat`

```
            List :: * → *        Nat :: *
           ─────────────────────────────────  K-App
                    List Nat :: *
```

### For `λα:*. α → α`

```
                       α:* ∈ {α:*}    α:* ∈ {α:*}
                      ─────────────  ─────────────
                       {α:*} ⊢ α::*   {α:*} ⊢ α::*
                      ───────────────────────────────  K-Arrow
                            {α:*} ⊢ α → α :: *
         ──────────────────────────────────────────────────  K-TyLam
               {} ⊢ λα:*. α → α :: * → *
```

### For Higher-Kinded Types

```
Functor : (* → *) → *

     F:(* → *)
         │
         ▼
    ∀α. (α → F α) → ...

Example:
  Functor List :: *
  Functor Maybe :: *
  Functor (Either String) :: *
```

---

## Type Operators as Functions

### List as Type Operator

```
List : * → *

List Nat     = [Nat]       (concrete list of Nats)
List Bool    = [Bool]      (concrete list of Bools)
List (List α) = [[α]]      (nested lists)

Type application tree:
          TyApp
         /     \
      List    Nat
       │
     * → *      *
       │
       └───────────► *
```

### Either as Binary Type Operator

```
Either : * → * → *

Either String Nat = String or Nat

Curried application:
  Either String : * → *        (partial application!)
  (Either String) Nat : *      (fully applied)

          TyApp
         /     \
      TyApp    Nat
     /     \
  Either  String
```

---

## Church Encodings at Kind Level

### Type-Level Natural Numbers

```
Zero = λF:*→*. λα:*. α              :: (* → *) → * → *
One  = λF:*→*. λα:*. F α            :: (* → *) → * → *
Two  = λF:*→*. λα:*. F (F α)        :: (* → *) → * → *

Visual:
  Zero F A = A               (apply F zero times)
  One  F A = F A             (apply F once)
  Two  F A = F (F A)         (apply F twice)
  Three F A = F (F (F A))    (apply F three times)
```

### Type-Level Successor

```
Succ = λN:((*→*)→*→*). λF:*→*. λα:*. F (N F α)

Succ Zero = λF. λα. F (Zero F α)
          = λF. λα. F α
          = One ✓
```

---

## Higher-Kinded Polymorphism

### Functor Type

```
Functor : (* → *) → *

In Haskell terms:
  class Functor f where
    fmap :: (a → b) → f a → f b

In F-omega:
  Functor F = ∀α:*. ∀β:*. (α → β) → F α → F β
```

### Monad Type

```
Monad : (* → *) → *

In Haskell:
  class Monad m where
    return :: a → m a
    (>>=)  :: m a → (a → m b) → m b

In F-omega:
  Monad M = (∀α. α → M α) × (∀α. ∀β. M α → (α → M β) → M β)
          = Return × Bind
```

---

## Type-Level Beta Reduction

```
(λα:*. α → α) Nat
      │
      ▼ type-level β-reduction
  [α ↦ Nat](α → α)
      │
      ▼
  Nat → Nat


More complex:
  (λF:*→*. λα:*. F (F α)) List Bool
      │
      ▼ reduce outer
  (λα:*. List (List α)) Bool
      │
      ▼ reduce inner
  List (List Bool)
      │
      = [[Bool]]
```

---

## Kind Checking Algorithm

```
kindOf(Δ, τ):

         ┌───────────┬───────────┬───────────┐
         │           │           │           │
         ▼           ▼           ▼           ▼
      TyVar      TyArrow     TyLam      TyApp
         │           │           │           │
         ▼           ▼           ▼           ▼
    lookup α    check both   check body  check both
    in Δ        sides :: *   with α:κ    and match
         │           │           │           │
         ▼           ▼           ▼           ▼
    return κ    return *    return      return
                            κ₁ → κ₂      κ₂
```

---

## Type Equality via Normalization

```
Are these types equal?

  (λα:*. α → α) Nat    ?=    Nat → Nat

Step 1: Normalize left side
  (λα:*. α → α) Nat  →  Nat → Nat

Step 2: Normalize right side
  Nat → Nat  (already normal)

Step 3: Compare
  Nat → Nat  =  Nat → Nat  ✓

Types are equal if their normal forms are identical.
```

---

## Reference Card

```
┌─────────────────────────────────────────────────────────────┐
│                   SYSTEM F-OMEGA                            │
├─────────────────────────────────────────────────────────────┤
│  KINDS                                                      │
│    κ ::= * | κ → κ                                         │
│                                                             │
│  TYPES                                                      │
│    τ ::= α | τ → τ | ∀α:κ. τ | λα:κ. τ | τ τ              │
│                                                             │
│  KIND RULES                                                 │
│    Δ, α:κ₁ ⊢ τ : κ₂                                        │
│    ─────────────────────  K-TyLam                          │
│    Δ ⊢ λα:κ₁. τ : κ₁ → κ₂                                  │
│                                                             │
│    Δ ⊢ τ₁ : κ₁ → κ₂    Δ ⊢ τ₂ : κ₁                        │
│    ────────────────────────────────  K-TyApp               │
│           Δ ⊢ τ₁ τ₂ : κ₂                                   │
│                                                             │
│  KEY INSIGHT                                                │
│    Types are now a lambda calculus with kinds!             │
│    Type-level computation via β-reduction                   │
└─────────────────────────────────────────────────────────────┘
```
