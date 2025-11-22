# Chapter 5: System F - Practice Problems

## Purpose
Practice explicit polymorphism, type abstraction/application, and understanding parametricity.

---

## Warm-Up Problems (15 minutes)

### Problem 1.1: Type Abstraction ⭐
Write explicit System F terms:

a) Polymorphic identity: `id : ∀A. A → A`
b) Const function: `const : ∀A B. A → B → A`
c) Flip: `flip : ∀A B C. (A → B → C) → B → A → C`

### Problem 1.2: Type Application ⭐
Apply these polymorphic functions:

a) `id [Nat] 42`
b) `const [Bool] [Nat] true 5`
c) `id [∀A. A → A] id`

### Problem 1.3: Church Encodings ⭐
Define Church encodings in System F:

a) `Bool = ∀A. A → A → A`
b) Write `true` and `false`
c) Write `if : ∀A. Bool → A → A → A`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Church Booleans ⭐⭐
Implement full boolean library:

a) `and : Bool → Bool → Bool`
b) `or : Bool → Bool → Bool`
c) `not : Bool → Bool`
d) Prove: `not (not b) = b` using parametricity

### Problem 2.2: Church Numerals ⭐⭐
Define Church numerals in System F:

a) `Nat = ∀A. (A → A) → A → A`
b) `zero : Nat`
c) `succ : Nat → Nat`
d) `add : Nat → Nat → Nat`
e) `mult : Nat → Nat → Nat`

### Problem 2.3: Church Pairs ⭐⭐
Implement polymorphic pairs:

a) `Pair A B = ∀C. (A → B → C) → C`
b) `pair : ∀A B. A → B → Pair A B`
c) `fst : ∀A B. Pair A B → A`
d) `snd : ∀A B. Pair A B → B`

### Problem 2.4: Church Lists ⭐⭐
Define polymorphic lists:

a) `List A = ∀B. (A → B → B) → B → B`
b) `nil : ∀A. List A`
c) `cons : ∀A. A → List A → List A`
d) `map : ∀A B. (A → B) → List A → List B`
e) `length : ∀A. List A → Nat`

### Problem 2.5: Option Type ⭐⭐
Implement polymorphic option:

a) `Option A = ∀B. B → (A → B) → B`
b) `none : ∀A. Option A`
c) `some : ∀A. A → Option A`
d) `map_option : ∀A B. (A → B) → Option A → Option B`
e) `bind_option : ∀A B. Option A → (A → Option B) → Option B`

### Problem 2.6: Either Type ⭐⭐
Implement polymorphic sum:

a) `Either A B = ∀C. (A → C) → (B → C) → C`
b) `left : ∀A B. A → Either A B`
c) `right : ∀A B. B → Either A B`
d) `either : ∀A B C. (A → C) → (B → C) → Either A B → C`

### Problem 2.7: Church Trees ⭐⭐
Binary trees in System F:

a) `Tree A = ∀B. (A → B) → (B → B → B) → B`
b) `leaf : ∀A. A → Tree A`
c) `node : ∀A. Tree A → Tree A → Tree A`
d) `map_tree : ∀A B. (A → B) → Tree A → Tree B`
e) `fold_tree : ∀A B. (A → B) → (B → B → B) → Tree A → B`

### Problem 2.8: Parametricity ⭐⭐
Use free theorems to prove:

a) For `f : ∀A. A → A`, prove `f [Nat] n = n`
b) For `g : ∀A. List A → List A`, what can you conclude?
c) For `h : ∀A B. A → B`, show this type is uninhabited (except ⊥)

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Existential Types ⭐⭐⭐
Using the encoding `∃A. T = ∀B. (∀A. T → B) → B`:

a) Encode abstract counters:
   ```
   Counter = ∃S. {
     init : S,
     inc : S → S,
     get : S → Nat
   }
   ```
b) Implement `Counter` with `Nat` representation
c) Implement `Counter` with Church numeral representation
d) Show client code can't distinguish implementations (abstraction!)

### Problem 3.2: Free Theorems ⭐⭐⭐
Derive free theorems for:

a) `map : ∀A B. (A → B) → List A → List B`
   - Prove: `map g . map f = map (g . f)`

b) `fold : ∀A B. (A → B → B) → B → List A → B`
   - State the free theorem

c) `traverse : ∀A B. (A → List B) → List A → List (List B)`
   - What properties follow from parametricity?

### Problem 3.3: Data Abstraction ⭐⭐⭐
Implement abstract data types:

a) **Abstract Stack**:
   ```
   Stack A = ∃S. {
     empty : S,
     push : A → S → S,
     pop : S → Option (A * S),
     isEmpty : S → Bool
   }
   ```

b) Implement with list representation

c) Prove client can't forge stack values (representation independence)

### Problem 3.4: Impredicativity ⭐⭐⭐
System F is impredicative (quantify over all types, including polymorphic ones):

a) Show: `id [∀A. A → A] id` is well-typed
b) Define self-application: `self_apply : (∀A. A → A) → (∀A. A → A)`
c) Contrast with predicative systems (why ML can't do this)
d) Explain why full type inference is undecidable in System F

---

## Debugging Exercises (30 minutes)

### Debug 1: Type Application ⭐⭐
Student wrote:
```
id 42    -- Missing type application!
```

Should be:
```
id [Nat] 42
```

Explain: Why is explicit type application needed in System F?

### Debug 2: Church Encoding Mismatch ⭐⭐
What's wrong?
```
Bool = ∀A. A → A → A
not = ΛA. λb:Bool. λx:A. λy:A. b y x

Error: b has type Bool, but used as function!
```

Fix: Need to apply `b` at type `A`:
```
not = ΛA. λb:Bool. λx:A. λy:A. b [A] y x
```

### Debug 3: Existential Unpacking ⭐⭐
Student's counter client:
```
let c = makeCounter in
  c.inc (c.init)    -- Error!
```

Problem: Can't access fields without unpacking existential.

Fix:
```
unpack {S, ops} = makeCounter in
  ops.inc ops.init
```

### Debug 4: Parametricity Violation ⭐⭐
Student claims:
```
sneaky : ∀A. A → Nat
sneaky = ΛA. λx:A. 42
```

Why is this well-typed? Doesn't it violate parametricity?

**A**: It's well-typed! But notice it IGNORES its argument (consistent with free theorem).

### Debug 5: Polymorphic Recursion ⭐⭐
This doesn't work in HM but works in System F:
```
f = ΛA. λx:A.
  ... f [Pair A A] (pair x x) ...
```

Explain:
- Why HM can't handle this
- Why System F can (explicit instantiation)
- When this pattern is useful

---

## Code Review Exercises (30 minutes)

### Review 1: Church vs ADT Booleans ⭐⭐
Compare:

**Church Encoding**:
```
Bool = ∀A. A → A → A
if = ΛA. λb:Bool. λt:A. λe:A. b [A] t e
```

**ADT Encoding** (if System F had them):
```
data Bool = True | False
if = λb:Bool. λt:A. λe:A. case b of
  True => t
| False => e
```

Discuss:
- Performance implications
- Ease of use
- Expressiveness

### Review 2: Map Implementations ⭐⭐
Two `map` implementations for Church lists:

**Version A** (direct):
```
map = ΛA B. λf:A→B. λxs:List A.
  ΛC. λcons:B→C→C. λnil:C.
    xs [C] (λa:A. λacc:C. cons (f a) acc) nil
```

**Version B** (using fold):
```
map = ΛA B. λf:A→B. λxs:List A.
  fold [A] [List B]
    (λa:A. λacc:List B. cons [B] (f a) acc)
    (nil [B])
    xs
```

Which is better? Are they equivalent?

### Review 3: Existential Encoding ⭐⭐⭐
Student encoded existentials two ways:

**Version A** (Church-style):
```
∃A. T = ∀B. (∀A. T → B) → B
```

**Version B** (direct):
```
pack {A, t} = ...  -- Built-in primitive
```

Discuss:
- Expressiveness (are they equivalent?)
- Implementation complexity
- Type safety guarantees

---

## Solutions

### Warm-Up

**1.1**:
```
a) id = ΛA. λx:A. x
b) const = ΛA B. λx:A. λy:B. x
c) flip = ΛA B C. λf:A→B→C. λy:B. λx:A. f x y
```

**1.2**:
```
a) 42 : Nat
b) true : Bool
c) (ΛA. λx:A. x) : ∀A. A → A
```

**1.3**:
```
a) Bool = ∀A. A → A → A
b) true = ΛA. λt:A. λf:A. t
   false = ΛA. λt:A. λf:A. f
c) if = ΛA. λb:Bool. λt:A. λe:A. b [A] t e
```

### Standard

**2.1**:
```
and = λp:Bool. λq:Bool.
  ΛA. λt:A. λf:A. p [A] (q [A] t f) f

or = λp:Bool. λq:Bool.
  ΛA. λt:A. λf:A. p [A] t (q [A] t f)

not = λb:Bool.
  ΛA. λt:A. λf:A. b [A] f t
```

**2.2**:
```
Nat = ∀A. (A → A) → A → A
zero = ΛA. λf:A→A. λx:A. x
succ = λn:Nat. ΛA. λf:A→A. λx:A. f (n [A] f x)
add = λm:Nat. λn:Nat. ΛA. λf:A→A. λx:A. m [A] f (n [A] f x)
mult = λm:Nat. λn:Nat. ΛA. m [A] (n [A])
```

**2.4**:
```
List A = ∀B. (A → B → B) → B → B
nil = ΛA B. λcons:A→B→B. λnil:B. nil
cons = ΛA. λx:A. λxs:List A.
  ΛB. λcons:A→B→B. λnil:B. cons x (xs [B] cons nil)

map = ΛA B. λf:A→B. λxs:List A.
  ΛC. λcons:B→C→C. λnil:C.
    xs [C] (λa:A. λacc:C. cons (f a) acc) nil
```

**2.5**:
```
Option A = ∀B. B → (A → B) → B
none = ΛA B. λn:B. λs:A→B. n
some = ΛA. λx:A. ΛB. λn:B. λs:A→B. s x

map_option = ΛA B. λf:A→B. λopt:Option A.
  opt [Option B] (none [B]) (λx:A. some [B] (f x))
```

**2.8**:
```
a) By parametricity, f can't inspect its argument, so must return it
b) Can only rearrange, not create/destroy elements
c) Can't produce B from A without additional information (uninhabited)
```

### Challenge

**3.1**:
```
Counter = ∃S. (S * (S → S) * (S → Nat))

-- Nat implementation
natCounter : Counter
natCounter = pack {Nat, (0, λn. n+1, λn. n)}

-- Church numeral implementation
churchCounter : Counter
churchCounter = pack {ChurchNat, (zero, succ, toNat)}
```

**3.2**:
```
a) For any f : A → B, g : B → C:
   map g . map f = map (g . f)

   Proof: By parametricity in the type ∀A B
```

**3.3**: Stack implementation uses existentials to hide representation

**3.4**: Impredicativity allows `∀A. A → A` to quantify over itself

### Debug

**Debug 1**: System F has no type inference for type applications (decidability)

**Debug 2**: Must apply Church-encoded data at appropriate types

**Debug 3**: Existentials require unpacking before accessing components

**Debug 4**: Returning constant is valid - parametricity says nothing about ignoring arguments

**Debug 5**: Polymorphic recursion needs explicit types; HM can't infer, F can check

### Review

**Review 1**: Church encoding is universal but less efficient; ADTs are more practical

**Review 2**: Both equivalent; B is more compositional

**Review 3**: Version A can encode Version B; equally expressive

---

**Time**: 4-6 hours
**Focus**: Explicit polymorphism and parametricity are the key new concepts
