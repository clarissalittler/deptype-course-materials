# Chapter 6: System F-omega - Practice Problems

## Purpose
Practice higher-kinded types, type operators, and kind checking.

---

## Warm-Up Problems (15 minutes)

### Problem 1.1: Kinds ⭐
What are the kinds of these types?

a) `Nat`
b) `List`
c) `∀A::*. A → A`
d) `λA::*. A → A`
e) `λA::*. λB::*. A → B → A`

### Problem 1.2: Type Operators ⭐
Define these type-level functions:

a) Identity: `λA::*. A`
b) Constant: `λA::*. λB::*. A`
c) Function composition (at type level): `(λF::*⇒*. λG::*⇒*. λA::*. F (G A))`

### Problem 1.3: Kind Errors ⭐
Which of these are well-kinded?

a) `List Nat` : `*`
b) `List List` : `*`
c) `List [Nat]` : `*`
d) `(λA::*⇒*. A A)`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Functor Type Class ⭐⭐
Define the Functor type operator:

a) `Functor :: (*⇒*) ⇒ *` where
   ```
   Functor F = ∀A B. (A → B) → F A → F B
   ```

b) Implement `Functor List`
c) Implement `Functor Option`
d) Implement `Functor Tree`

### Problem 2.2: Monad Type Class ⭐⭐
Define Monad type operator:

a) `Monad :: (*⇒*) ⇒ *` where
   ```
   Monad M = {
     return : ∀A. A → M A,
     bind : ∀A B. M A → (A → M B) → M B
   }
   ```

b) Implement `Monad Option`
c) Implement `Monad List`
d) Prove monad laws for Option

### Problem 2.3: Type-Level Lists ⭐⭐
Define type-level list operations:

a) `TList :: * ⇒ *` (kind of lists)
b) `TNil :: ∀A::*. TList A`
c) `TCons :: ∀A::*. A → TList A → TList A`
d) `TMap :: (*⇒*) ⇒ TList * ⇒ TList *`
   - Maps type operator over type-level list

### Problem 2.4: Type-Level Natural Numbers ⭐⭐
Encode natural numbers at type level:

a) Define kind `Nat :: kind`
b) `Zero :: Nat`
c) `Succ :: Nat ⇒ Nat`
d) `Plus :: Nat ⇒ Nat ⇒ Nat`

Then define:
```
Vec :: * ⇒ Nat ⇒ *
```
Type of vectors parameterized by length!

### Problem 2.5: Fixed Points ⭐⭐
Define type-level fixed point:

a) `Fix :: (*⇒*) ⇒ *` where `Fix F = F (Fix F)`

b) Use to define recursive types:
   - `List A = Fix (λX. Unit + (A * X))`
   - `Tree A = Fix (λX. A + (X * X))`

c) Show how to fold over `Fix F`

### Problem 2.6: Functor Composition ⭐⭐
Define composition of functors:

a) `Compose :: (*⇒*) ⇒ (*⇒*) ⇒ (*⇒*)` where
   ```
   Compose F G = λA::*. F (G A)
   ```

b) Show that composition of functors is a functor:
   ```
   Functor F ∧ Functor G ⇒ Functor (Compose F G)
   ```

c) Implement `fmap` for `Compose F G`

### Problem 2.7: Natural Transformations ⭐⭐
Define natural transformations:

a) `Nat :: (*⇒*) ⇒ (*⇒*) ⇒ *` where
   ```
   Nat F G = ∀A::*. F A → G A
   ```

b) Implement:
   - `listToOption : Nat List Option` (head)
   - `optionToList : Nat Option List` (singleton or empty)

c) Show naturality: `nt . fmap_F f = fmap_G f . nt`

### Problem 2.8: Higher-Kinded Polymorphism ⭐⭐
Implement polymorphic over type constructors:

a) `map_pair :: ∀F::*⇒*. Functor F ⇒ ∀A B. (A → B) → (F A * F A) → (F B * F B)`

b) `sequence :: ∀F::*⇒*. Monad F ⇒ ∀A. List (F A) → F (List A)`

c) `traverse :: ∀F::*⇒*. Functor F ⇒ ∀A B. (A → F B) → List A → F (List B)`

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Kind Polymorphism ⭐⭐⭐
System F-omega doesn't have kind polymorphism, but we can simulate:

a) Define `Id :: ∀κ. κ ⇒ κ` (requires kind polymorphism)

b) Without kind polymorphism, define separate:
   - `IdType :: * ⇒ *`
   - `IdTypeOp :: (*⇒*) ⇒ (*⇒*)`

c) Explain the limitation and how System Fω̲ (with kind polymorphism) helps

### Problem 3.2: Type-Level Programming ⭐⭐⭐
Implement type-level computation:

a) **Type-level arithmetic**:
   ```
   Plus :: Nat ⇒ Nat ⇒ Nat
   Mult :: Nat ⇒ Nat ⇒ Nat
   ```

b) **Type-level comparison**:
   ```
   LEQ :: Nat ⇒ Nat ⇒ Bool
   ```

c) **Sized vectors**:
   ```
   Vec :: * ⇒ Nat ⇒ *
   append :: ∀A::*. ∀m n::Nat. Vec A m → Vec A n → Vec A (Plus m n)
   ```

### Problem 3.3: GADTs Preview ⭐⭐⭐
Generalized Algebraic Data Types can be encoded:

a) Define well-typed expressions:
   ```
   Expr :: * ⇒ * where
     Lit :: Nat → Expr Nat
     Bool :: Bool → Expr Bool
     If :: ∀A. Expr Bool → Expr A → Expr A → Expr A
     Add :: Expr Nat → Expr Nat → Expr Nat
   ```

b) Implement type-safe evaluator:
   ```
   eval :: ∀A. Expr A → A
   ```

c) Show why STLC couldn't do this

### Problem 3.4: Monad Transformers ⭐⭐⭐
Define monad transformers:

a) `MaybeT :: (*⇒*) ⇒ (*⇒*)` where
   ```
   MaybeT M A = M (Option A)
   ```

b) Show `MaybeT M` is a monad if `M` is:
   ```
   Monad M ⇒ Monad (MaybeT M)
   ```

c) Define lift:
   ```
   lift :: ∀M::*⇒*. Monad M ⇒ ∀A. M A → MaybeT M A
   ```

d) Implement `StateT` and `ReaderT`

---

## Debugging Exercises (30 minutes)

### Debug 1: Kind Mismatch ⭐⭐
Student wrote:
```
Compose :: (*⇒*) ⇒ * ⇒ (*⇒*)
Compose F G = λA::*. F (G A)

Error: G has kind *, but used as *⇒*
```

Fix: `Compose :: (*⇒*) ⇒ (*⇒*) ⇒ (*⇒*)`

### Debug 2: Type Operator Application ⭐⭐
What's wrong?
```
List :: *⇒*
xs :: List
```

**A**: `List` is a type operator, needs argument: `xs :: List Nat`

### Debug 3: Functor Instance ⭐⭐
Student's functor for `Pair`:
```
Functor (Pair A) -- Error! What kind is Pair?
```

Need to define:
```
Pair :: * ⇒ *⇒*
FPair A :: *⇒*   -- partially applied
Functor (FPair A)  -- Now works!
```

### Debug 4: Fixed Point Infinite Loop? ⭐⭐
Student worried about:
```
Fix :: (*⇒*) ⇒ *
Fix F = F (Fix F) = F (F (Fix F)) = ...
```

**A**: This is fine! Type-level infinite unfolding is OK (lazy at type level). Only value-level divergence is problematic.

### Debug 5: Natural Transformation ⭐⭐
Student wrote:
```
listHead :: List A → Option A

Error: Not polymorphic over A!
```

Should be:
```
listHead :: ∀A::*. List A → Option A
```

Natural transformations require explicit polymorphism.

---

## Code Review Exercises (30 minutes)

### Review 1: Functor vs Bifunctor ⭐⭐
Compare:

**Functor**:
```
Functor :: (*⇒*) ⇒ *
fmap :: ∀F::*⇒*. Functor F ⇒ ∀A B. (A → B) → F A → F B
```

**Bifunctor**:
```
Bifunctor :: (*⇒*⇒*) ⇒ *
bimap :: ∀F::*⇒*⇒*. Bifunctor F ⇒
  ∀A B C D. (A → C) → (B → D) → F A B → F C D
```

When to use each?

### Review 2: Free Monad ⭐⭐⭐
Two approaches to free monad:

**Version A** (direct):
```
Free :: (*⇒*) ⇒ (*⇒*) where
  Pure :: ∀F::*⇒*. ∀A. A → Free F A
  Free :: ∀F::*⇒*. ∀A. F (Free F A) → Free F A
```

**Version B** (as fixed point):
```
Free F = Fix (λX. λA. A + F X)
```

Are they equivalent? Which is better?

### Review 3: Type-Level vs Value-Level ⭐⭐⭐
Student asks: "Why compute at type level vs value level?"

Compare:
```
-- Value level
length :: ∀A. List A → Nat

-- Type level
Vec :: * ⇒ Nat ⇒ *
-- Length encoded in type!
```

Discuss:
- Compile-time guarantees
- Runtime performance
- Complexity vs safety tradeoff

---

## Solutions

### Warm-Up

**1.1**:
- a) `*` (proper type)
- b) `* ⇒ *` (type operator)
- c) `*` (polymorphic type)
- d) `* ⇒ *` (type operator)
- e) `* ⇒ * ⇒ *` (binary type operator)

**1.2**:
```
a) λA::*. A : * ⇒ *
b) λA::*. λB::*. A : * ⇒ * ⇒ *
c) λF::*⇒*. λG::*⇒*. λA::*. F (G A) : (*⇒*) ⇒ (*⇒*) ⇒ (*⇒*)
```

**1.3**:
- a) ✓ `*`
- b) ✗ `List` expects `*`, got `*⇒*`
- c) ✓ `*` (assuming `[Nat]` syntax for `List Nat`)
- d) ✗ `A A` requires `A :: * ⇒ *` and `A :: *` (contradiction)

### Standard

**2.1**:
```
Functor F = ∀A B::*. (A → B) → F A → F B

functorList :: Functor List
functorList = ΛA B. λf:A→B. λxs:List A.
  map [A] [B] f xs
```

**2.2**:
```
Monad M = {
  return : ∀A. A → M A,
  bind : ∀A B. M A → (A → M B) → M B
}

monadOption :: Monad Option
monadOption = {
  return = ΛA. λx:A. some [A] x,
  bind = ΛA B. λma:Option A. λf:A→Option B.
    ma [Option B] (none [B]) f
}
```

**2.5**:
```
Fix :: (*⇒*) ⇒ *
Fix F = ∀A. (F A → A) → A

fold :: ∀F::*⇒*. Fix F → ∀A. (F A → A) → A
fold = λfx:Fix F. fx
```

**2.6**:
```
Compose :: (*⇒*) ⇒ (*⇒*) ⇒ (*⇒*)
Compose F G = λA::*. F (G A)

fmap_compose :: ∀F G::*⇒*. Functor F ⇒ Functor G ⇒
  Functor (Compose F G)
fmap_compose = ΛA B. λf:A→B.
  fmap_F (fmap_G f)
```

**2.8**:
```
sequence :: ∀F::*⇒*. Monad F ⇒ ∀A. List (F A) → F (List A)
sequence = ΛA. λxs:List (F A).
  xs [F (List A)]
    (λfa:F A. λfacc:F (List A).
      bind [A] [List A] fa (λa:A.
        bind [List A] [List A] facc (λacc:List A.
          return [List A] (cons a acc))))
    (return [List A] nil)
```

### Challenge

**3.1**: Kind polymorphism would allow `∀κ. κ ⇒ κ` (System Fω̲)

**3.2**:
```
Vec :: * ⇒ Nat ⇒ *

append :: ∀A::*. ∀m n::Nat. Vec A m → Vec A n → Vec A (Plus m n)
-- Type signature encodes length invariant!
```

**3.3**: GADTs allow different constructors to return different type indices

**3.4**: Monad transformers compose monadic effects

### Debug

**Debug 1**: Kind signatures must match kind usage

**Debug 2**: Type operators are not types until fully applied

**Debug 3**: Partial application changes kind

**Debug 4**: Type-level recursion is fine (compile-time only)

**Debug 5**: Natural transformations must be explicitly polymorphic

### Review

**Review 1**: Functor for unary constructors, Bifunctor for binary

**Review 2**: Both equivalent; direct is clearer

**Review 3**: Type-level gives compile-time safety, value-level is simpler

---

**Time**: 4-6 hours
**Focus**: Understanding kinds is essential for type operators
