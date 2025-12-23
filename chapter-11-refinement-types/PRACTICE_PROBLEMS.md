# Chapter 11: Refinement Types - Practice Problems

## Purpose
Additional practice beyond the main exercises to reinforce refinement type concepts.

**Difficulty Legend**: ⭐ Easy | ⭐⭐ Medium | ⭐⭐⭐ Hard

---

## Warm-Up Problems (15-20 minutes)

### Problem 1.1: Basic Refinements ⭐
Write refinement types for:

a) Even natural numbers
b) Natural numbers between 10 and 20 (inclusive)
c) Natural numbers that are multiples of 5
d) Boolean values that are always true

### Problem 1.2: Type Inhabitants ⭐
How many values inhabit each type?

a) `{x: Nat | x < 3}`
b) `{x: Bool | x == true}`
c) `{x: Nat | x > 0 && x < 1}`
d) `{x: Nat | false}`

### Problem 1.3: Subtyping Check ⭐
True or false? If true, explain the implication.

a) `{x: Nat | x > 5}` <: `{x: Nat | x > 0}`
b) `{x: Nat | x == 10}` <: `{x: Nat | x > 5}`
c) `{x: Nat | x > 0}` <: `{x: Nat | x > 5}`
d) `{x: Nat | x > 0 && x < 10}` <: `{x: Nat | x < 100}`

### Problem 1.4: Reading Types ⭐
What does each function type guarantee?

a) `safeSqrt : {n: Nat | n >= 0} -> Nat`
b) `nonEmpty : List a -> {xs: List a | length xs > 0}`
c) `increment : {n: Nat | n < 100} -> {m: Nat | m <= 100}`
d) `choose : {xs: List a | length xs > 0} -> a`

### Problem 1.5: Predicate Validity ⭐
Are these implications valid?

a) `x > 5 ⟹ x > 0`
b) `x == 10 ⟹ x > 100`
c) `x > 0 && x < 10 ⟹ x > 0`
d) `false ⟹ x > 1000`

---

## Standard Problems (45-60 minutes)

### Problem 2.1: Safe Division ⭐⭐
Write types and implementations for:

a) **safeDiv**: Division requiring non-zero divisor
b) **safeMod**: Modulo requiring non-zero divisor
c) **divBy10**: Division by 10 (always safe!)

Test cases:
- `safeDiv 10 2` → `5`
- Type checker rejects: `safeDiv 10 0`

### Problem 2.2: List Operations ⭐⭐
Write refinement types for:

a) **safeHead**: Returns first element (requires non-empty list)
b) **safeTail**: Returns all but first (requires non-empty list)
c) **safeLast**: Returns last element (requires non-empty list)
d) **safeInit**: Returns all but last (requires non-empty list)

### Problem 2.3: Array Indexing ⭐⭐
Given `type Array n a = {arr: [a] | length arr == n}`:

a) Write type for **get**: Safe array access at index
b) Write type for **set**: Safe array update at index
c) Write type for **resize**: Change array size
d) Why can't we have out-of-bounds errors with these types?

### Problem 2.4: Path Sensitivity ⭐⭐
For each function, determine what refinement `x` has in each branch:

```
a) λx : Nat. if x > 10 then A else B
   -- then branch: x has type ???
   -- else branch: x has type ???

b) λx : Nat. if iszero x then A else B
   -- then branch: x has type ???
   -- else branch: x has type ???

c) λx : Nat. if x >= 5 && x <= 15 then A else B
   -- then branch: x has type ???
   -- else branch: x has type ???
```

### Problem 2.5: Strengthening and Weakening ⭐⭐
Given a value of the first type, can it be used as the second type?

a) `{x: Nat | x == 5}` → `{x: Nat | x > 0}`
b) `{x: Nat | x > 0}` → `{x: Nat | x == 5}`
c) `{x: Nat | x > 10 && x < 20}` → `{x: Nat | x > 5}`
d) `{x: Nat | x > 5}` → `{x: Nat | x > 10 && x < 20}`

### Problem 2.6: Dependent Functions ⭐⭐
Write dependent function types for:

a) **replicate**: Takes `n` and value, returns list of length `n`
b) **take**: Takes `n` and list, returns first `n` elements
c) **drop**: Takes `n` and list, returns all but first `n` elements
d) **split**: Takes `n` and list of length `n+m`, returns two lists

### Problem 2.7: Predicate Design ⭐⭐
Design refinement types for:

a) **Sorted lists**: Lists where elements are in order
b) **Unique lists**: Lists with no duplicates
c) **Balanced trees**: Trees where subtree heights differ by at most 1
d) **Valid dates**: Natural numbers representing dates (YYYYMMDD format)

Hint: You may need helper predicates like `isSorted`, `hasNoDups`, etc.

### Problem 2.8: Combining Refinements ⭐⭐
Is the following subtyping valid? Explain.

```
{x: Nat | x > 10} ∩ {x: Nat | x < 20}  <:  {x: Nat | x > 5 && x < 100}
```

Where `∩` means intersection (both refinements must hold).

---

## Challenge Problems (60-90 minutes)

### Problem 3.1: Maximum Function ⭐⭐⭐
Write a type for `max` that expresses:
- Takes two natural numbers
- Returns a value greater than or equal to both inputs
- The result is one of the inputs

Can you express this with refinement types?

### Problem 3.2: Smart Constructors ⭐⭐⭐
Implement a module for positive numbers:

```
module Positive where
  type Pos = {n: Nat | n > 0}

  -- Smart constructor: returns Maybe because not all Nats are positive
  mkPos : Nat -> Maybe Pos

  -- Operations that preserve positivity
  add : Pos -> Pos -> Pos
  mult : Pos -> Pos -> Pos

  -- Unsafe operations
  sub : Pos -> Pos -> Nat  -- Result might not be positive
  div : Pos -> Pos -> Nat  -- Integer division
```

Implement each function and explain why each type is correct.

### Problem 3.3: Liquid Types Inference ⭐⭐⭐
Infer the most precise refinement type for:

```
mystery = λf. λx.
  if x > 0
  then f x
  else 0
```

What is the type of `f`? What is the type of `x`? What refinement does the result have?

### Problem 3.4: Invariant Preservation ⭐⭐⭐
Given sorted list type: `type Sorted a = {xs: List a | isSorted xs}`

Write refinement types proving these preserve sortedness:

a) **insert**: Insert element into sorted list maintaining order
b) **merge**: Merge two sorted lists into one sorted list
c) **sort**: Convert any list to sorted list
d) **filter**: Filter sorted list (stays sorted)

### Problem 3.5: Path Sensitivity Limits ⭐⭐⭐
Why can't the type checker accept this?

```
problem : Nat -> Nat
problem = λx.
  let y = if x > 5 then x else x + 10 in
  pred y  -- Error: y might be 0!
```

The programmer knows `y > 0` always, but the type checker doesn't. Why? How could you fix it?

---

## Debugging Exercises (30 minutes)

### Debug 1: Type Error ⭐
This doesn't type check. Why?

```
bad : Nat -> {n: Nat | n > 0}
bad = λx. x
```

### Debug 2: Subtyping Error ⭐⭐
Why does this fail?

```
weaken : {x: Nat | x > 10} -> {x: Nat | x > 5}
weaken = λx. x  -- OK

strengthen : {x: Nat | x > 5} -> {x: Nat | x > 10}
strengthen = λx. x  -- ERROR!
```

### Debug 3: Path Sensitivity Issue ⭐⭐
Why doesn't this work?

```
safePred : Nat -> Nat
safePred = λx.
  let b = iszero x in
  if b then 0 else pred x  -- ERROR: x might be 0
```

Hint: The condition is not directly `iszero x`.

### Debug 4: Predicate Too Weak ⭐⭐
This claims to be safe but isn't:

```
almostSafeDiv : Nat -> Nat -> Nat
almostSafeDiv = λn. λd.
  if d > 0 || d < 0  -- Oops!
  then n `quot` d
  else 0
```

What's wrong with the guard? How should it be fixed?

### Debug 5: Dependent Type Confusion ⭐⭐
Why is this rejected?

```
mkPair : (n: Nat) -> {m: Nat | m == n} -> (Nat, Nat)
mkPair = λn. λm. (n, m + 1)  -- ERROR
```

---

## Code Review Exercises (30 minutes)

### Review 1: Division Safety ⭐⭐
Review this division implementation:

```
safeDivision : Nat -> Nat -> Maybe Nat
safeDivision = λn. λd.
  if d == 0
  then Nothing
  else Just (n `quot` d)
```

Questions:
- Is this safe?
- Could we use refinement types to avoid `Maybe`?
- Write a better type signature using refinements

### Review 2: List Head ⭐⭐
Compare two implementations:

**Version A**:
```
head : List a -> Maybe a
head = λxs. case xs of
  [] -> Nothing
  (x:_) -> Just x
```

**Version B**:
```
head : {xs: List a | length xs > 0} -> a
head = λxs. case xs of
  (x:_) -> x
```

Which is better? When would you use each?

### Review 3: Bounded Increment ⭐⭐
Review this function:

```
boundedInc : {n: Nat | n < 100} -> {m: Nat | m < 100}
boundedInc = λn. n + 1
```

Is this type correct? If not, what's wrong and how to fix?

### Review 4: Predicate Complexity ⭐⭐⭐
A student wrote:

```
type ValidDate = {d: Nat | isValidDate d}

where isValidDate d =
  let year = d / 10000 in
  let month = (d / 100) % 100 in
  let day = d % 100 in
  year >= 1900 && year <= 2100 &&
  month >= 1 && month <= 12 &&
  day >= 1 && day <= daysInMonth month year
```

Questions:
- Will this work with our type checker?
- Is it decidable?
- How would you simplify this?

---

## Design Problems (45 minutes)

### Design 1: State Machine ⭐⭐⭐
Design refinement types for a file handle state machine:

States: Closed, Open, Error
Operations:
- `open : {f: File | isClosed f} -> {f: File | isOpen f}`
- `read : {f: File | isOpen f} -> (String, File)`
- `close : {f: File | isOpen f} -> {f: File | isClosed f}`

How do refinements prevent reading a closed file?

### Design 2: Safe Buffer ⭐⭐⭐
Design a safe buffer API:

```
type Buffer n = {buf: Array n Byte}

write : (buf: Buffer n, i: ???, byte: Byte) -> Buffer n
read : (buf: Buffer n, i: ???) -> Byte
resize : Buffer n -> (m: Nat) -> Buffer m
```

What refinements should `i` have for safe access?

### Design 3: Arithmetic Expression Evaluator ⭐⭐⭐
Design types for an arithmetic evaluator that prevents:
- Division by zero
- Negative numbers (only natural arithmetic)
- Overflow (values must stay under 1000)

```
data Expr = Lit Nat | Add Expr Expr | Sub Expr Expr | Div Expr Expr

eval : Expr -> ???
```

What type should `eval` have?

---

## Solutions

### Warm-Up Solutions

**1.1**:
```
a) {x: Nat | x % 2 == 0}  (or {x: Nat | exists k. x == 2 * k})
b) {x: Nat | x >= 10 && x <= 20}
c) {x: Nat | x % 5 == 0}  (or {x: Nat | exists k. x == 5 * k})
d) {x: Bool | x == true}
```

**1.2**:
```
a) 3 values: {0, 1, 2}
b) 1 value: {true}
c) 0 values (empty type - no natural number strictly between 0 and 1)
d) 0 values (false is never satisfiable)
```

**1.3**:
```
a) True: x > 5 ⟹ x > 0
b) True: x == 10 ⟹ x > 5 (since 10 > 5)
c) False: 3 > 0 but not 3 > 5
d) True: (x > 0 && x < 10) ⟹ x < 100
```

**1.4**:
```
a) Input must be non-negative (always true for Nat)
b) Takes any list, returns non-empty list (adds element?)
c) Input < 100, output ≤ 100 (increment that might hit limit)
d) Takes non-empty list, returns an element
```

**1.5**:
```
a) Valid: if x > 5 then certainly x > 0
b) Invalid: 10 is not > 100
c) Valid: conjunction elimination
d) Valid: false implies anything (vacuously true)
```

### Standard Solutions

**2.1**:
```
a) safeDiv : Nat -> {d: Nat | d > 0} -> Nat
   safeDiv = λn. λd. n `quot` d

b) safeMod : Nat -> {d: Nat | d > 0} -> Nat
   safeMod = λn. λd. n `mod` d

c) divBy10 : Nat -> Nat
   divBy10 = λn. n `quot` 10
```

**2.2**:
```
a) safeHead : {xs: List a | length xs > 0} -> a
b) safeTail : {xs: List a | length xs > 0} -> List a
c) safeLast : {xs: List a | length xs > 0} -> a
d) safeInit : {xs: List a | length xs > 0} -> List a
```

**2.3**:
```
a) get : (arr: Array n a, i: {i: Nat | i < n}) -> a
b) set : (arr: Array n a, i: {i: Nat | i < n}, val: a) -> Array n a
c) resize : Array n a -> (m: Nat) -> Array m a
d) The index refinement {i: Nat | i < n} ensures i is always in bounds!
```

**2.4**:
```
a) then: {x: Nat | x > 10}, else: {x: Nat | x <= 10}
b) then: {x: Nat | x == 0}, else: {x: Nat | x > 0}
c) then: {x: Nat | x >= 5 && x <= 15}, else: {x: Nat | x < 5 || x > 15}
```

**2.5**:
```
a) Yes: 5 > 0, so subtyping is valid
b) No: not all positive numbers equal 5
c) Yes: (x > 10 && x < 20) ⟹ x > 5
d) No: 7 > 5 but not (7 > 10 && 7 < 20)
```

**2.6**:
```
a) replicate : (n: Nat) -> a -> {xs: List a | length xs == n}
b) take : (n: Nat) -> {xs: List a | length xs >= n} -> {ys: List a | length ys == n}
c) drop : (n: Nat) -> {xs: List a | length xs >= n} -> List a
d) split : (n: Nat) -> {xs: List a | length xs >= n} -> ({ys: List a | length ys == n}, List a)
```

**2.7**:
```
a) {xs: List a | isSorted xs}
b) {xs: List a | hasNoDups xs}
c) {t: Tree a | isBalanced t}
d) {d: Nat | d >= 19000101 && d <= 21001231 && isValidDate d}
```

**2.8**: Yes, valid. If x > 10 and x < 20, then certainly x > 5 and x < 100.

### Challenge Solutions

**3.1**:
```
max : (a: Nat, b: Nat) -> {m: Nat | m >= a && m >= b && (m == a || m == b)}
```

**3.2**:
```
mkPos n = if n > 0 then Just n else Nothing  -- Cast to Pos when > 0
add a b = a + b                               -- Sum of positives is positive
mult a b = a * b                              -- Product of positives is positive
sub a b = if a >= b then a - b else 0        -- Might not be positive
div a b = a `quot` b                         -- Integer division
```

**3.3**:
```
mystery : ∀a. (a -> Nat) -> {x: Nat | x >= 0} -> Nat

Actually, more precisely:
mystery : ({x: Nat | x > 0} -> Nat) -> Nat -> Nat

Result refinement: Result >= 0 always
```

**3.4**:
```
a) insert : a -> Sorted a -> Sorted a
b) merge : Sorted a -> Sorted a -> Sorted a
c) sort : List a -> Sorted a
d) filter : (a -> Bool) -> Sorted a -> Sorted a
```

**3.5**: The join point loses path information. Type checker sees:
- If branch: `x` (could be anything)
- Else branch: `x + 10`
- Join: Could be `x` if `x <= 5`, but then `y` might be 0

Fix: Add assertion or restructure to maintain refinements.

### Debugging Solutions

**Debug 1**: Not all Nat are > 0. Need: `{x: Nat | x > 0} -> {n: Nat | n > 0}`

**Debug 2**: Weakening is fine (more specific to less specific). Strengthening fails because not all values > 5 are > 10.

**Debug 3**: Condition `b` is not syntactically `iszero x`, so path sensitivity doesn't apply. Fix:
```
safePred x = if iszero x then 0 else pred x
```

**Debug 4**: `d > 0 || d < 0` is always true for integers but `d` can be 0! Should be `d != 0` or just `d > 0` for Nat.

**Debug 5**: Result type says `(Nat, Nat)` but needs `(n, n)` to satisfy the dependent type. The `m + 1` breaks the equality.

---

**Estimated Time**: 4-6 hours for all problems
**Difficulty Distribution**: 5 easy, 8 medium, 5 hard, 5 debug, 4 review, 3 design

**Note**: These problems complement the main exercises. Focus on understanding refinements as predicates and subtyping via implication!
