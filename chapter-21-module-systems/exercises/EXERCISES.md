# Exercises: Module Systems

These exercises will help you master module systems concepts.

## Exercise 1: Basic Structures (⭐)

**Task:** Create a structure representing a 2D point with fields `x` and `y`, both of type `Nat`.

**Expected signature:**
```ocaml
sig
  val x : Nat
  val y : Nat
end
```

<details>
<summary>Hint</summary>

Use the `struct ... end` syntax with `val` declarations.
</details>

---

## Exercise 2: Type Definitions (⭐)

**Task:** Create a structure that:
1. Defines a type `coordinate = Nat`
2. Has two values `x : coordinate` and `y : coordinate`

<details>
<summary>Hint</summary>

Use `type` declaration followed by `val` declarations that use the defined type.
</details>

---

## Exercise 3: Signature Matching (⭐⭐)

**Task:** Given this signature:
```ocaml
sig
  type t
  val value : t
  val increment : t -> t
end
```

Create a structure that matches it, using `Nat` as the underlying representation for `t`.

<details>
<summary>Hint</summary>

Define `type t = Nat`, then implement `value` and `increment` using natural number operations.
</details>

---

## Exercise 4: Sealing for Information Hiding (⭐⭐)

**Task:** Create a sealed module `Secret` that:
1. Internally uses `type password = Nat`
2. Exports `password` as an abstract type
3. Provides `val create : Nat -> password`
4. Provides `val verify : password -> Nat -> Bool`
5. Hides the internal representation

<details>
<summary>Hint</summary>

Create a structure with concrete implementations, then seal it with a signature that makes `password` abstract (don't use `= Nat` in the signature).
</details>

---

## Exercise 5: Simple Functor (⭐⭐)

**Task:** Write a functor `Successor` that:
- Takes a module with `sig val n : Nat end`
- Returns a module with `val next : Nat` equal to `succ n`

Test it with: `(Successor)(struct val n : Nat = 5 end)`

Expected result: `struct val next : Nat = 6 end`

<details>
<summary>Hint</summary>

Use `functor(X : sig val n : Nat end) => struct val next : Nat = succ X.n end`
</details>

---

## Exercise 6: Parameterized Container (⭐⭐⭐)

**Task:** Write a functor `MakeBox` that:
- Takes a module `Elem : sig type t end`
- Returns a module with:
  - `type elem = Elem.t`
  - `type box = {content: elem}`
  - `val make : elem -> box`
  - `val get : box -> elem`

<details>
<summary>Hint</summary>

The functor body should define all four components. Use record type for `box`.
</details>

---

## Exercise 7: Abstract Stack (⭐⭐⭐)

**Task:** Implement an abstract stack module with:
- Abstract type `stack`
- `val empty : stack` (represented as `0`)
- `val push : Nat -> stack -> stack` (use `succ` to increment)
- `val isEmpty : stack -> Bool` (use `iszero`)
- `val size : stack -> Nat` (identity function)

Use sealing to hide that `stack = Nat`.

<details>
<summary>Hint</summary>

1. Create structure with `type stack = Nat` and implementations
2. Seal with signature having `type stack` (abstract, no `= Nat`)
</details>

---

## Exercise 8: Nested Modules (⭐⭐)

**Task:** Create a module `Math` with two nested modules:
- `Basic`: with `val id : Nat -> Nat` (identity function)
- `Advanced`: with `val double : Nat -> Nat` (use `succ` twice)

<details>
<summary>Hint</summary>

Use `module` declarations inside a `struct`:
```ocaml
struct
  module Basic = struct ... end
  module Advanced = struct ... end
end
```
</details>

---

## Exercise 9: Functor with Type (⭐⭐⭐)

**Task:** Write a functor `MakeCounter` that:
- Takes `Base : sig type t; val zero : t end`
- Returns a module with:
  - `type counter = Base.t`
  - `val initial : counter = Base.zero`

<details>
<summary>Hint</summary>

Reference the parameter's type as `Base.t` and value as `Base.zero`.
</details>

---

## Exercise 10: Multiple Component Signature (⭐⭐⭐)

**Task:** Create a module matching this signature:
```ocaml
sig
  type key = Nat
  type value = Bool
  type entry = {k: key, v: value}
  val make : key -> value -> entry
end
```

<details>
<summary>Hint</summary>

Define the types in order, then implement `make` using lambda and record syntax.
</details>

---

## Exercise 11: Functor Composition (⭐⭐⭐⭐)

**Task:** Given:
```ocaml
F = functor(X : sig val n : Nat end) => struct val m : Nat = succ X.n end
G = functor(Y : sig val m : Nat end) => struct val p : Nat = succ Y.m end
```

Compose them: apply F to `struct val n : Nat = 0 end`, then apply G to the result.

What is the final value of `p`?

<details>
<summary>Hint</summary>

`(G)((F)(struct val n : Nat = 0 end))`

Trace: n=0 → m=1 → p=2
</details>

---

## Exercise 12: Width Subtyping (⭐⭐)

**Task:** Show that this signature matching succeeds:
```ocaml
struct
  val x : Nat = 5
  val y : Nat = 10
  val z : Bool = true
end
:> sig
  val x : Nat
  val y : Nat
end
```

Why does it work even though `z` is not in the signature?

<details>
<summary>Answer</summary>

Width subtyping: a module can have MORE components than the signature requires. Extra components (like `z`) are hidden by sealing.
</details>

---

## Exercise 13: Two-Parameter Functor (⭐⭐⭐⭐)

**Task:** Write a functor that takes TWO modules:
- `X : sig type t end`
- `Y : sig type u end`

And returns a module with `type pair = {fst: X.t, snd: Y.u}`.

<details>
<summary>Hint</summary>

Nest functors:
```ocaml
functor(X : sig type t end) =>
  functor(Y : sig type u end) =>
    struct type pair = {fst: X.t, snd: Y.u} end
```
</details>

---

## Exercise 14: Abstract Type with Operations (⭐⭐⭐⭐)

**Task:** Create a sealed `Counter` module where:
- `counter` is abstract (internally `Nat`)
- Operations: `zero : counter`, `inc : counter -> counter`, `dec : counter -> counter`, `toNat : counter -> Nat`
- Ensure `counter` remains abstract in the signature

<details>
<summary>Hint</summary>

Structure: concrete implementations with `type counter = Nat`
Signature: abstract type `type counter` (no `= Nat`)
Operations use `succ`, `pred`, and identity
</details>

---

## Exercise 15: Dependent Module (⭐⭐⭐⭐⭐)

**Task:** Create a structure with:
- `module Base = struct type t = Nat val zero : t = 0 end`
- `module Extended = struct type u = Base.t val one : u = succ Base.zero end`

Access: `Extended.one` should work and have type `Extended.u` (which equals `Base.t` = `Nat`).

<details>
<summary>Hint</summary>

Nested modules can reference earlier modules. Use `Base.t` and `Base.zero` in `Extended`.
</details>

---

## Challenge Exercises

### Challenge 1: Generic List Functor (⭐⭐⭐⭐⭐)

**Task:** If we had proper list types, write a functor for a generic list module. For now, design the signature:

```ocaml
sig
  type elem
  type list
  val empty : list
  val cons : elem -> list -> list
  val isEmpty : list -> Bool
end
```

What would the functor signature be?

<details>
<summary>Answer</summary>

```ocaml
functor(Element : sig type t end) =>
  sig
    type elem = Element.t
    type list
    val empty : list
    val cons : elem -> list -> list
    val isEmpty : list -> Bool
  end
```
</details>

---

### Challenge 2: Module Equivalence (⭐⭐⭐⭐⭐)

**Task:** Are these two modules equivalent?

```ocaml
M1 = (struct type t = Nat val x : t = 0 end
      :> sig type t val x : t end)

M2 = (struct type t = Nat val x : t = 0 end
      :> sig type t val x : t end)
```

Can you assign `M1.x` to a variable of type `M2.t`?

<details>
<summary>Answer</summary>

No! Even though they have the same structure and signature, each sealing creates a DISTINCT abstract type. `M1.t` ≠ `M2.t`. This is called **generativity** - each sealing generates a fresh abstract type.
</details>

---

### Challenge 3: Higher-Order Functor (⭐⭐⭐⭐⭐)

**Task:** Can you write a functor that takes another functor as an argument?

Example signature:
```ocaml
functor(F : functor(X : S1) => S2) =>
  functor(Y : S3) =>
    (F)(Y)
```

Is this possible in our system?

<details>
<summary>Answer</summary>

Our simple system doesn't support higher-order functors (functors taking functors). This requires more advanced module calculi like F-ing modules. SML doesn't support it either, but some research languages do.
</details>

---

## Solutions

See `exercises/Solutions.hs` for complete solutions to all exercises.

## Testing Your Solutions

You can test your solutions in the REPL:

```bash
stack run module-systems-repl
```

Then paste your module definitions and check the signatures.

## Grading Criteria

For each exercise, check:
1. ✅ **Correctness**: Does it type check?
2. ✅ **Signature**: Does it match the expected signature?
3. ✅ **Abstraction**: Are types properly hidden (when required)?
4. ✅ **Functionality**: Do the operations work as expected?

## Additional Practice

1. Implement more abstract data types (Queue, Set, Map)
2. Write functors for sorting, searching
3. Create a small library with nested modules
4. Design signatures for real-world interfaces
5. Practice functor composition

## Further Reading

- [README.md](../README.md) - Theory and typing rules
- [TUTORIAL.md](../TUTORIAL.md) - Step-by-step guide
- [FAQ.md](../FAQ.md) - Common questions
- [QUICK_START.md](../QUICK_START.md) - Quick reference

Good luck! 🚀
