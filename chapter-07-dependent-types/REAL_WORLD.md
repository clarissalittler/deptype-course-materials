# Chapter 7: Real-World Connections

## Where Dependent Types Appear

### Idris

```idris
-- Length-indexed vectors
data Vect : Nat -> Type -> Type where
  Nil  : Vect 0 a
  (::) : a -> Vect n a -> Vect (S n) a

-- Type depends on value!
append : Vect n a -> Vect m a -> Vect (n + m) a
append Nil       ys = ys
append (x :: xs) ys = x :: append xs ys

-- Safe head (can't be called on empty!)
head : Vect (S n) a -> a
head (x :: _) = x
```

### Agda

```agda
-- Dependent function type
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

-- Function type includes the length
lookup : ∀ {A n} → Fin n → Vec A n → A
lookup zero    (x ∷ _)  = x
lookup (suc i) (_ ∷ xs) = lookup i xs
```

### Coq

```coq
(* Dependent pairs for refinement *)
Definition positive := { n : nat | n > 0 }.

(* Length-indexed lists *)
Inductive vec (A : Type) : nat -> Type :=
  | vnil : vec A 0
  | vcons : forall n, A -> vec A n -> vec A (S n).
```

### Lean 4

```lean
-- Vectors with length in type
def Vector (α : Type) (n : Nat) := { l : List α // l.length = n }

-- Dependent function
def replicate : (n : Nat) → α → Vector α n :=
  fun n a => ⟨List.replicate n a, List.length_replicate n a⟩
```

---

## Approximating Dependent Types

### TypeScript: Branded Types

```typescript
// Simulate refinement with brands
type PositiveNumber = number & { readonly __brand: 'positive' };

function makePositive(n: number): PositiveNumber | null {
  return n > 0 ? n as PositiveNumber : null;
}

function sqrt(n: PositiveNumber): number {
  return Math.sqrt(n);  // Safe! n is guaranteed positive
}
```

### TypeScript: Literal Types

```typescript
// Type-level numbers (limited)
type Length<T extends any[]> = T['length'];

type Two = Length<[1, 2]>;  // 2

// Tuple of exact length
type Tuple<T, N extends number> = N extends N
  ? number extends N
    ? T[]
    : _Tuple<T, N, []>
  : never;

type _Tuple<T, N extends number, R extends T[]> =
  R['length'] extends N ? R : _Tuple<T, N, [T, ...R]>;

type ThreeNumbers = Tuple<number, 3>;  // [number, number, number]
```

### Rust: Const Generics

```rust
// Arrays with length in type
fn first<T, const N: usize>(arr: [T; N]) -> Option<&T>
where
    [T; N]: Sized,
{
    if N > 0 { Some(&arr[0]) } else { None }
}

// Matrix multiplication with size checking
fn matmul<const M: usize, const N: usize, const P: usize>(
    a: [[f64; N]; M],
    b: [[f64; P]; N],
) -> [[f64; P]; M] {
    // Sizes are checked at compile time!
    // ...
}
```

### Haskell: GADTs and Type Families

```haskell
{-# LANGUAGE GADTs, DataKinds, TypeFamilies #-}

-- Natural numbers at type level
data Nat = Zero | Succ Nat

-- Length-indexed vectors
data Vec (n :: Nat) a where
  VNil  :: Vec 'Zero a
  VCons :: a -> Vec n a -> Vec ('Succ n) a

-- Safe head
vhead :: Vec ('Succ n) a -> a
vhead (VCons x _) = x

-- Type-level addition
type family Plus (m :: Nat) (n :: Nat) :: Nat where
  Plus 'Zero     n = n
  Plus ('Succ m) n = 'Succ (Plus m n)
```

---

## Practical Applications

### 1. Safe Array Access

**Without Dependent Types (Runtime Error)**:
```javascript
const arr = [1, 2, 3];
arr[10];  // undefined - no compile error!
```

**With Dependent Types (Compile Error)**:
```idris
lookup : Fin n -> Vect n a -> a
-- Fin n can only hold values 0..n-1

xs : Vect 3 Int
xs = [1, 2, 3]

lookup 2 xs  -- OK: 2 < 3
lookup 5 xs  -- Compile error! 5 is not a valid Fin 3
```

### 2. Protocol Compliance

```idris
-- State machine in types
data DoorState = Open | Closed

data Door : DoorState -> Type where
  MkDoor : Door state

openDoor : Door Closed -> Door Open
closeDoor : Door Open -> Door Closed

-- Can't close an already closed door!
-- closeDoor (closeDoor door)  -- Type error!
```

### 3. Units of Measure (F#)

```fsharp
[<Measure>] type m   // meters
[<Measure>] type s   // seconds
[<Measure>] type kg  // kilograms

let distance : float<m> = 100.0<m>
let time : float<s> = 9.58<s>
let speed : float<m/s> = distance / time

// Can't add incompatible units
// distance + time  // Compile error!
```

### 4. Database Queries (Persistent/Esqueleto)

```haskell
-- Type-safe queries
selectList
  :: (PersistEntity record, PersistEntityBackend record ~ SqlBackend)
  => [Filter record]
  -> [SelectOpt record]
  -> SqlPersistT m [Entity record]

-- Type guarantees:
-- - Only valid filters for this entity
-- - Return type matches entity type
```

---

## The Curry-Howard Correspondence in Practice

### Proofs as Programs

```idris
-- "A implies B" is a function A -> B
-- A proof of "A implies A" is the identity function
proof_A_implies_A : a -> a
proof_A_implies_A x = x

-- "A and B implies A" is a projection
proof_And_elim : (a, b) -> a
proof_And_elim (x, _) = x

-- "A implies (A or B)" is left injection
proof_Or_intro : a -> Either a b
proof_Or_intro x = Left x
```

### Theorem Proving

```coq
(* Prove that addition is commutative *)
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.
```

---

## Why Type-in-Type is Dangerous

### The Problem

```
Type : Type  -- Allows paradox!

-- Can encode Russell's paradox
R = { T : Type | T ∉ T }
-- Is R ∈ R?
```

### Real Languages Avoid This

| Language | Solution |
|----------|----------|
| Coq | Universe hierarchy (Set, Prop, Type) |
| Agda | Universe polymorphism (Set₀, Set₁, ...) |
| Lean | Universe levels |
| Idris | Universe checking |

---

## Tools and Languages

### Full Dependent Types
- **Agda**: Proof assistant, research
- **Coq**: Proof assistant, verified software
- **Idris**: Practical programming with DT
- **Lean**: Math proofs, programming

### Partial Support
- **Haskell**: GADTs, type families, singletons
- **Rust**: Const generics (limited)
- **TypeScript**: Conditional types (very limited)
- **F#**: Units of measure

### Verification Tools
- **Liquid Haskell**: Refinement types for Haskell
- **Dafny**: Verification-aware language
- **F***: Effectful verification
- **ATS**: Practical dependent types

---

## When to Use Dependent Types

### Good Use Cases

1. **Safety-critical code**: Aerospace, medical
2. **Cryptographic protocols**: Prove security properties
3. **Compilers**: Prove transformations correct
4. **Financial systems**: Ensure invariants hold

### Overkill For

1. **CRUD apps**: Too much ceremony
2. **Prototypes**: Slows development
3. **Simple scripts**: Not worth the complexity

---

## Key Takeaways for Practitioners

1. **Types can depend on values**: `Vec n a` knows its length

2. **Eliminates classes of bugs**: No out-of-bounds, no null

3. **Proofs are programs**: Write functions that prove theorems

4. **Universe hierarchies prevent paradox**: No `Type : Type`

5. **Mainstream adoption is growing**: Rust const generics, TypeScript advances

---

## Further Reading

- *Type-Driven Development with Idris* - Edwin Brady
- *Certified Programming with Dependent Types* - Adam Chlipala (Coq)
- *Programming Language Foundations in Agda* - Wadler & Kokke
- Software Foundations series (Coq)
