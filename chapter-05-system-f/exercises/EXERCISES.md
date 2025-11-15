# Chapter 5 Exercises: System F (Polymorphic Lambda Calculus)

## Exercise 1: Church Encodings (Easy-Medium)

Implement the following using System F's Church encodings:

### 1a. Option Type
```
Option α = ∀R. R → (α → R) → R

none : ∀α. Option α
none = ΛA. λn:R. λs:A→R. n

some : ∀α. α → Option α
some = ΛA. λx:A. ΛR. λn:R. λs:A→R. s x

match : ∀α. ∀R. Option α → R → (α → R) → R
match = ΛA. ΛR. λopt:Option A. λn:R. λs:A→R. opt [R] n s
```

### 1b. Either Type
```
Either α β = ∀R. (α → R) → (β → R) → R

left : ∀α. ∀β. α → Either α β
right : ∀α. ∀β. β → Either α β
match : ∀α. ∀β. ∀R. Either α β → (α → R) → (β → R) → R
```

## Exercise 2: Polymorphic Data Structures (Medium)

### 2a. Binary Trees
```
Tree α = ∀R. R → (α → R → R → R) → R

leaf : ∀α. Tree α
leaf = ΛA. ΛR. λl:R. λn:A→R→R→R. l

node : ∀α. α → Tree α → Tree α → Tree α
node = ΛA. λx:A. λleft:Tree A. λright:Tree A.
  ΛR. λl:R. λn:A→R→R→R. n x (left [R] l n) (right [R] l n)
```

Implement:
- `map : ∀α. ∀β. (α → β) → Tree α → Tree β`
- `fold : ∀α. ∀β. β → (α → β → β → β) → Tree α → β`
- `height : ∀α. Tree α → CNat`

### 2b. Rose Trees
Define rose trees (trees with arbitrary branching):
```
RoseTree α = ∀R. (α → List R → R) → R
```

## Exercise 3: Church Numerals Extended (Medium)

### 3a. Exponentiation
```
exp : CNat → CNat → CNat
exp m n = n [CNat] (mult m) one
```

### 3b. Factorial
Implement factorial using your fixed-point combinator from the solutions.

### 3c. Division
```
div : CNat → CNat → CNat
```
Implement integer division (saturating to 0 for division by 0).

## Exercise 4: Existential Types (Hard)

### 4a. Encode Existentials
Using the encoding `∃α. τ ≡ ∀R. (∀α. τ → R) → R`, implement:

```
pack : ∀α. τ → (∃α. τ)
unpack : (∃α. τ) → ∀R. (∀α. τ → R) → R
```

### 4b. Abstract Counter
Implement an abstract counter ADT:

```
Counter = ∃α. {
  new  : α,
  inc  : α → α,
  get  : α → Nat
}

makeCounter : Counter
```

The internal representation (α) is hidden from clients.

### 4c. Stack ADT
```
Stack = ∃α. {
  empty : α,
  push  : Nat → α → α,
  pop   : α → Option (Nat × α),
  size  : α → Nat
}
```

## Exercise 5: Parametricity (Hard)

### 5a. Free Theorems
Prove these free theorems from types alone:

1. Any `f : ∀α. List α → List α` either:
   - Returns the empty list
   - Returns the input list unchanged
   - Returns a permutation/prefix/suffix of the input

2. Any `f : ∀α. ∀β. (α → β) → List α → List β` must be `map` (up to order/duplicates).

3. Any `f : ∀α. α → α` must be the identity function.

### 5b. Naturality
Show that for `map : ∀α. ∀β. (α → β) → List α → List β`:
```
map g ∘ map f = map (g ∘ f)
```

This follows from parametricity alone!

## Exercise 6: Impredicativity (Hard)

### 6a. Self-Application
Show that the polymorphic identity can be applied to itself:
```
id : ∀α. α → α
id [∀β. β → β] id : ∀β. β → β
```

### 6b. Type-Level Functions
Create a "type-level function" that takes a type and returns a function type:
```
F = Λα. α → α

id : ∀α. F α
id = Λα. λx:α. x
```

### 6c. Nested Polymorphism
```
twice : ∀α. (α → α) → α → α
twice = Λα. λf:α→α. λx:α. f (f x)

polyTwice : (∀α. α → α) → (∀β. β → β)
polyTwice = λf:(∀α. α→α). Λβ. twice [β] (f [β])
```

## Exercise 7: System F Limitations (Hard)

### 7a. Non-Definable Functions
Show that these functions cannot be defined in System F:

1. Type case: `typeCase : ∀α. α → (if α=Nat then Bool else α)`
2. Equality: `eq : ∀α. α → α → Bool`

Explain why parametricity prevents these.

### 7b. Need for Extensions
Explain why we need:
- Recursive types for lists/trees
- Base types for practical programming
- Type operators (System F-omega) for type-level abstraction

## Solutions

See `Solutions.hs` for reference implementations.

## Testing

```bash
stack test --test-arguments "--match 'Chapter 5'"
```

## Learning Objectives

- Master explicit polymorphism
- Understand Church encodings deeply
- Learn about existential types
- Grasp parametricity and free theorems
- Recognize System F's power and limitations

## References

- Girard (1972): Original System F thesis
- Reynolds (1974): "Towards a Theory of Type Structure"
- Reynolds (1983): "Types, Abstraction and Parametric Polymorphism"
- Wadler (1989): "Theorems for Free!"
- Pierce TAPL Chapters 23-24: "Universal Types" and "Existential Types"
- Pierce & Turner (2000): "Local Type Inference"
- Dunfield & Krishnaswami (2013): "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"
