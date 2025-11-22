# Chapter 3: STLC with Algebraic Data Types - Tutorial

## Introduction

Welcome to the ADT tutorial! In this chapter, we extend STLC with the power to build complex, type-safe data structures. You'll learn the patterns that appear in every modern statically-typed language.

**The Big Ideas**:
- **Products** (×): Combine multiple values into one
- **Sums** (+): Choose between alternatives
- **Pattern Matching**: Safely extract data from structures

Think of this as unlocking "structs/classes" and "enums/unions" with mathematical precision and compiler-verified safety.

---

## Part 1: Product Types - Combining Values

### What is a Product Type?

A **product type** `τ₁ × τ₂` represents a pair of values: one of type `τ₁` and one of type `τ₂`.

**Intuition**: If you have 3 possible values of type `τ₁` and 4 possible values of type `τ₂`, then `τ₁ × τ₂` has 3 × 4 = 12 possible values. That's why it's called a "product"!

### Real-World Analogy

In JavaScript/TypeScript:
```typescript
type Pair = [boolean, number];  // Product type
const pair: Pair = [true, 42];
```

In Rust:
```rust
type Pair = (bool, u32);  // Tuple
let pair: Pair = (true, 42);
```

In lambda calculus with ADTs:
```
τ = Bool × Nat
t = (true, 42)
```

### Creating Pairs

**Syntax**: `(t₁, t₂)`

**Example 1**: Create a pair of a boolean and a number
```
(true, 0) : Bool × Nat
```

**Example 2**: Create a pair of two numbers
```
(succ 0, succ (succ 0)) : Nat × Nat
```

**Example 3**: Nest pairs (like tuples!)
```
((true, 0), false) : (Bool × Nat) × Bool
```

### Typing Rule for Pairs

```
Γ ⊢ t₁ : τ₁    Γ ⊢ t₂ : τ₂
────────────────────────────  (T-Pair)
Γ ⊢ (t₁, t₂) : τ₁ × τ₂
```

**Reading**: If `t₁` has type `τ₁` and `t₂` has type `τ₂`, then the pair `(t₁, t₂)` has type `τ₁ × τ₂`.

### Worked Example: Type Check a Pair

Type check: `(if true then 0 else 1, false)`

**Step 1**: Type the first element
```
Γ ⊢ true : Bool    Γ ⊢ 0 : Nat    Γ ⊢ 1 : Nat
─────────────────────────────────────────────  (T-If)
Γ ⊢ if true then 0 else 1 : Nat
```

**Step 2**: Type the second element
```
─────────────────  (T-False)
Γ ⊢ false : Bool
```

**Step 3**: Apply T-Pair
```
Γ ⊢ if true then 0 else 1 : Nat    Γ ⊢ false : Bool
──────────────────────────────────────────────────────  (T-Pair)
Γ ⊢ (if true then 0 else 1, false) : Nat × Bool
```

**Result**: Type is `Nat × Bool` ✓

### Extracting from Pairs: fst and snd

**First projection**: `fst (t₁, t₂)` → `t₁`
**Second projection**: `snd (t₁, t₂)` → `t₂`

**Example 1**:
```
fst (true, 0)  →  true
```

**Example 2**:
```
snd (true, 0)  →  0
```

### Typing Rules for Projections

```
Γ ⊢ t : τ₁ × τ₂
───────────────  (T-Fst)
Γ ⊢ fst t : τ₁


Γ ⊢ t : τ₁ × τ₂
───────────────  (T-Snd)
Γ ⊢ snd t : τ₂
```

### Worked Example: Type Check a Projection

Type check: `fst (λx:Nat. (x, true)) 0`

**Step 1**: Type the function
```
x:Nat ⊢ x : Nat    x:Nat ⊢ true : Bool
─────────────────────────────────────  (T-Pair)
x:Nat ⊢ (x, true) : Nat × Bool
────────────────────────────────────────────  (T-Abs)
∅ ⊢ λx:Nat. (x, true) : Nat → (Nat × Bool)
```

**Step 2**: Type the application
```
∅ ⊢ λx:Nat. (x, true) : Nat → (Nat × Bool)    ∅ ⊢ 0 : Nat
───────────────────────────────────────────────────────────  (T-App)
∅ ⊢ (λx:Nat. (x, true)) 0 : Nat × Bool
```

**Step 3**: Type fst
```
∅ ⊢ (λx:Nat. (x, true)) 0 : Nat × Bool
──────────────────────────────────────  (T-Fst)
∅ ⊢ fst (λx:Nat. (x, true)) 0 : Nat
```

**Result**: Type is `Nat` ✓

### Functions Returning Pairs

You can write functions that return multiple values using pairs!

**Example**: Function that returns both a number and its successor
```
λx:Nat. (x, succ x) : Nat → (Nat × Nat)
```

**Usage**:
```
(λx:Nat. (x, succ x)) 0  →  (0, 1)
```

---

## Part 2: Sum Types and Case Analysis

### What is a Sum Type?

A **sum type** `τ₁ + τ₂` represents a choice: either a value of type `τ₁` OR a value of type `τ₂`.

**Intuition**: If you have 3 possible values of type `τ₁` and 4 possible values of type `τ₂`, then `τ₁ + τ₂` has 3 + 4 = 7 possible values. That's why it's called a "sum"!

### Real-World Analogy

In Rust:
```rust
enum Either<A, B> {
    Left(A),
    Right(B)
}
let value: Either<bool, u32> = Either::Left(true);
```

In TypeScript:
```typescript
type Either<A, B> = { kind: 'left', value: A } | { kind: 'right', value: B };
const value: Either<boolean, number> = { kind: 'left', value: true };
```

In lambda calculus with ADTs:
```
τ = Bool + Nat
t = inl[Nat] true    (left alternative)
t = inr[Bool] 0      (right alternative)
```

### Creating Sum Values: inl and inr

**Left injection**: `inl[τ₂] t : τ₁ + τ₂` (when `t : τ₁`)
**Right injection**: `inr[τ₁] t : τ₁ + τ₂` (when `t : τ₂`)

**Why type annotations?** The type checker needs to know the "other" type!

**Example 1**: Inject boolean on the left
```
inl[Nat] true : Bool + Nat
```
This is "either a Bool or a Nat, and I'm choosing Bool (true)"

**Example 2**: Inject number on the right
```
inr[Bool] 0 : Bool + Nat
```
This is "either a Bool or a Nat, and I'm choosing Nat (0)"

### Typing Rules for Injections

```
Γ ⊢ t : τ₁
─────────────────────  (T-Inl)
Γ ⊢ inl[τ₂] t : τ₁ + τ₂


Γ ⊢ t : τ₂
─────────────────────  (T-Inr)
Γ ⊢ inr[τ₁] t : τ₁ + τ₂
```

### Case Analysis: Extracting from Sums

To use a sum type, you must handle **both** cases:

```
case t of
  inl x₁ => t₁
| inr x₂ => t₂
```

**Reading**:
- If `t` evaluates to `inl v`, bind `v` to `x₁` and evaluate `t₁`
- If `t` evaluates to `inr v`, bind `v` to `x₂` and evaluate `t₂`

### Typing Rule for Case

```
Γ ⊢ t : τ₁ + τ₂    Γ, x₁:τ₁ ⊢ t₁ : τ    Γ, x₂:τ₂ ⊢ t₂ : τ
────────────────────────────────────────────────────────────  (T-Case)
Γ ⊢ case t of inl x₁ => t₁ | inr x₂ => t₂ : τ
```

**Critical**: Both branches must return the same type `τ`!

### Worked Example: Type Check a Case Expression

Type check:
```
case (inl[Nat] true) of
  inl b => b
| inr n => iszero n
```

**Step 1**: Type the scrutinee (thing being matched)
```
∅ ⊢ true : Bool
───────────────────────  (T-Inl)
∅ ⊢ inl[Nat] true : Bool + Nat
```

**Step 2**: Type the left branch (assuming `b:Bool`)
```
b:Bool ∈ {b:Bool}
─────────────────  (T-Var)
b:Bool ⊢ b : Bool
```

**Step 3**: Type the right branch (assuming `n:Nat`)
```
n:Nat ⊢ n : Nat
─────────────────────  (T-IsZero)
n:Nat ⊢ iszero n : Bool
```

**Step 4**: Apply T-Case
```
∅ ⊢ inl[Nat] true : Bool + Nat    b:Bool ⊢ b : Bool    n:Nat ⊢ iszero n : Bool
─────────────────────────────────────────────────────────────────────────────────  (T-Case)
∅ ⊢ case (inl[Nat] true) of inl b => b | inr n => iszero n : Bool
```

**Result**: Type is `Bool` ✓

Both branches return `Bool`, so this type checks!

### Evaluation of Case Expressions

**Rule 1**: If scrutinee is `inl v`
```
case (inl[τ₂] v) of inl x₁ => t₁ | inr x₂ => t₂  →  [x₁ ↦ v]t₁
```

**Rule 2**: If scrutinee is `inr v`
```
case (inr[τ₁] v) of inl x₁ => t₁ | inr x₂ => t₂  →  [x₂ ↦ v]t₂
```

**Example**:
```
case (inl[Nat] true) of inl b => b | inr n => iszero n
→  [b ↦ true](b)
→  true
```

---

## Part 3: The Option Type Pattern

### Why Option Types?

In many languages, `null` represents "no value". But `null` is unsafe:
```javascript
const user = getUser(id);  // Might return null
console.log(user.name);    // Runtime error if null!
```

**Solution**: Make absence explicit in the type!

### Encoding Option with Sum Types

```
Option τ = Unit + τ

none : Option τ
none = inl[τ] ()

some : τ → Option τ
some = λx:τ. inr[Unit] x
```

**Why Unit?** We need a type with exactly one value to represent "nothing".

### Using Option Types

**Example 1**: Safe division
```
safeDivide : Nat → Nat → Option Nat
safeDivide = λm:Nat. λn:Nat.
  if iszero n
    then none
    else some m  -- (simplified - actual division would go here)
```

**Example 2**: Getting value or default
```
getOrDefault : τ → Option τ → τ
getOrDefault = λdefault:τ. λopt:Option τ.
  case opt of
    inl u => default
  | inr x => x
```

### Worked Example: Using getOrDefault

```
getOrDefault 42 (some 7)
=  (λdefault:Nat. λopt:Option Nat.
     case opt of inl u => default | inr x => x) 42 (some 7)
→  (λopt:Option Nat. case opt of inl u => 42 | inr x => x) (some 7)
→  (λopt:Option Nat. case opt of inl u => 42 | inr x => x) (inr[Unit] 7)
→  case (inr[Unit] 7) of inl u => 42 | inr x => x
→  [x ↦ 7]x
→  7
```

### Worked Example: Using getOrDefault with none

```
getOrDefault 42 none
=  (λdefault:Nat. λopt:Option Nat.
     case opt of inl u => default | inr x => x) 42 none
→  (λopt:Option Nat. case opt of inl u => 42 | inr x => x) (inl[Nat] ())
→  case (inl[Nat] ()) of inl u => 42 | inr x => x
→  [u ↦ ()]42
→  42
```

### Option Map: Transform Values Inside Option

```
mapOption : (τ₁ → τ₂) → Option τ₁ → Option τ₂
mapOption = λf:τ₁→τ₂. λopt:Option τ₁.
  case opt of
    inl u => none
  | inr x => some (f x)
```

**Example**:
```
mapOption (λx:Nat. succ x) (some 0)
→  case (inr[Unit] 0) of inl u => none | inr x => some (succ x)
→  some (succ 0)
→  some 1
```

---

## Part 4: Records - Named Products

### What are Records?

Records are like products, but with **named fields** instead of positions.

**Product**: `fst (0, true)` - which element did we get? The first one.
**Record**: `{x=0, y=true}.x` - we get the `x` field. Much clearer!

### Record Syntax

**Type**: `{l₁:τ₁, l₂:τ₂, ..., lₙ:τₙ}`
**Term**: `{l₁=t₁, l₂=t₂, ..., lₙ=tₙ}`
**Projection**: `t.l`

### Examples

**Example 1**: Define a Point type
```
Point = {x:Nat, y:Nat}

origin : Point
origin = {x=0, y=0}
```

**Example 2**: Access fields
```
origin.x  →  0
origin.y  →  0
```

**Example 3**: Function using records
```
getX : Point → Nat
getX = λp:Point. p.x
```

### Typing Rules for Records

**Formation**:
```
Γ ⊢ t₁ : τ₁    ...    Γ ⊢ tₙ : τₙ
─────────────────────────────────────  (T-Record)
Γ ⊢ {l₁=t₁,...,lₙ=tₙ} : {l₁:τ₁,...,lₙ:τₙ}
```

**Projection**:
```
Γ ⊢ t : {..., lⱼ:τⱼ, ...}
─────────────────────────  (T-Proj)
Γ ⊢ t.lⱼ : τⱼ
```

### Worked Example: Type Check Record Operations

Type check:
```
λp:{x:Nat, y:Nat}. {x=p.y, y=p.x}
```

This is a function that swaps x and y coordinates!

**Step 1**: Type the body under context `p:{x:Nat, y:Nat}`

Type `p.y`:
```
p:{x:Nat, y:Nat} ⊢ p : {x:Nat, y:Nat}
────────────────────────────────────  (T-Proj)
p:{x:Nat, y:Nat} ⊢ p.y : Nat
```

Type `p.x`:
```
p:{x:Nat, y:Nat} ⊢ p : {x:Nat, y:Nat}
────────────────────────────────────  (T-Proj)
p:{x:Nat, y:Nat} ⊢ p.x : Nat
```

Type the record:
```
p:{x:Nat, y:Nat} ⊢ p.y : Nat    p:{x:Nat, y:Nat} ⊢ p.x : Nat
────────────────────────────────────────────────────────────  (T-Record)
p:{x:Nat, y:Nat} ⊢ {x=p.y, y=p.x} : {x:Nat, y:Nat}
```

**Step 2**: Apply T-Abs
```
p:{x:Nat, y:Nat} ⊢ {x=p.y, y=p.x} : {x:Nat, y:Nat}
──────────────────────────────────────────────────────────────────────  (T-Abs)
∅ ⊢ λp:{x:Nat, y:Nat}. {x=p.y, y=p.x} : {x:Nat, y:Nat} → {x:Nat, y:Nat}
```

**Result**: Type is `{x:Nat, y:Nat} → {x:Nat, y:Nat}` ✓

---

## Part 5: Variants - Named Sums and State Machines

### What are Variants?

Variants are like sums, but with **named alternatives** (tags) instead of just inl/inr.

**Sum**: `inl[Nat] true` - which alternative? The left one.
**Variant**: `<happy=true> as Mood` - the `happy` alternative. Much clearer!

### Variant Syntax

**Type**: `<l₁:τ₁, l₂:τ₂, ..., lₙ:τₙ>`
**Term**: `<lᵢ=t> as <l₁:τ₁, ..., lₙ:τₙ>`
**Case**: `case t of <l₁=x₁> => t₁ | ... | <lₙ=xₙ> => tₙ`

### Example: Mood Type

```
Mood = <happy:Bool, sad:Bool, neutral:Unit>

makeHappy : Bool → Mood
makeHappy = λb:Bool. <happy=b> as Mood

makeSad : Bool → Mood
makeSad = λb:Bool. <sad=b> as Mood

makeNeutral : Mood
makeNeutral = <neutral=()> as Mood
```

### Pattern Matching on Variants

```
describeMood : Mood → Bool
describeMood = λm:Mood.
  case m of
    <happy=b> => b
  | <sad=b> => not b
  | <neutral=u> => false
```

### Example: Shape Type

```
Shape = <circle:Nat, square:Nat, rectangle:{width:Nat, height:Nat}>

makeCircle : Nat → Shape
makeCircle = λr:Nat. <circle=r> as Shape

makeSquare : Nat → Shape
makeSquare = λs:Nat. <square=s> as Shape

makeRectangle : Nat → Nat → Shape
makeRectangle = λw:Nat. λh:Nat. <rectangle={width=w, height=h}> as Shape
```

### State Machines with Variants

Variants are perfect for modeling state machines!

```
ConnectionState = <idle:Unit,
                   connecting:Nat,
                   connected:{id:Nat, time:Nat},
                   error:Bool>

handleState : ConnectionState → Bool
handleState = λstate:ConnectionState.
  case state of
    <idle=u> => true
  | <connecting=attempts> => iszero attempts
  | <connected=info> => true
  | <error=critical> => not critical
```

### Worked Example: Type Check Variant Case

Type check:
```
case (<circle=5> as Shape) of
  <circle=r> => r
| <square=s> => s
| <rectangle=dims> => dims.width
```

All branches return `Nat`, so this type checks to `Nat`.

---

## Part 6: Lists and Recursive Data

### The List Type

Lists are our first **recursive** data type - defined in terms of itself!

**Type**: `List τ` - a list of elements of type τ

**Constructors**:
- `[]` - empty list
- `t::ts` - cons (prepend element `t` to list `ts`)

### Creating Lists

**Example 1**: Empty list
```
[] : List Nat
```

**Example 2**: Single element
```
0 :: [] : List Nat
```

**Example 3**: Multiple elements
```
0 :: 1 :: 2 :: [] : List Nat
```

This is the list [0, 1, 2]

### Pattern Matching on Lists

```
match xs with
  [] => <base case>
| x::rest => <recursive case using x and rest>
```

### Worked Example: Length Function

```
length : List Nat → Nat
length = λxs:List Nat.
  match xs with
    [] => 0
  | x::rest => succ (length rest)
```

**Evaluation** of `length (0 :: 1 :: [])`:
```
length (0 :: 1 :: [])
→  match (0 :: 1 :: []) with [] => 0 | x::rest => succ (length rest)
→  succ (length (1 :: []))
→  succ (match (1 :: []) with [] => 0 | x::rest => succ (length rest))
→  succ (succ (length []))
→  succ (succ (match [] with [] => 0 | x::rest => succ (length rest)))
→  succ (succ 0)
→  2
```

### Worked Example: Append Function

```
append : List τ → List τ → List τ
append = λxs:List τ. λys:List τ.
  match xs with
    [] => ys
  | x::rest => x :: (append rest ys)
```

**Evaluation** of `append (0::[]) (1::[])`:
```
append (0::[]) (1::[])
→  match (0::[]) with [] => (1::[]) | x::rest => x :: (append rest (1::[]))
→  0 :: (append [] (1::[]))
→  0 :: (match [] with [] => (1::[]) | x::rest => x :: (append rest (1::[])))
→  0 :: (1::[])
→  0 :: 1 :: []
```

Result: The list [0, 1]

---

## Part 7: Advanced Pattern Matching

### Nested Patterns

You can nest patterns to match deep structures:

**Example 1**: Match a pair in a list
```
match xs with
  [] => ...
| (x, y)::rest => ...  // Pattern: pair inside cons
```

**Example 2**: Match first two elements
```
match xs with
  [] => ...
| x::[] => ...
| x::y::rest => ...  // Pattern: at least two elements
```

**Example 3**: Match nested pairs
```
match p with
  ((x, y), z) => ...  // Pattern: pair of (pair and element)
```

### Exhaustiveness Checking

A pattern match is **exhaustive** if it covers all possible cases.

**Exhaustive** ✓:
```
match opt with
  inl u => ...
| inr x => ...
```
Covers both constructors of sum type.

**Non-exhaustive** ✗:
```
match opt with
  inl u => ...
```
Missing the `inr` case!

**Exhaustive for lists** ✓:
```
match xs with
  [] => ...
| x::rest => ...
```
Covers both constructors (nil and cons).

### Wildcard Patterns

Use `_` when you don't need the value:

```
match pair with
  (_, y) => y  // Ignore first element, extract second
```

```
match xs with
  [] => 0
| _::rest => succ (length rest)  // Don't need the head value
```

---

## Part 8: Type Safety Proofs with ADTs

### Progress Theorem

**Theorem**: If `⊢ t : τ`, then either `t` is a value or there exists `t'` such that `t → t'`.

**Extension to ADTs**: We add new value forms and reduction rules:

**New Values**:
- Pairs: `(v₁, v₂)`
- Injections: `inl[τ] v`, `inr[τ] v`
- Records: `{l₁=v₁, ..., lₙ=vₙ}`
- Variants: `<l=v> as τ`
- Lists: `[]`, `v::vs`

**New Reductions**:
- `fst (v₁, v₂) → v₁`
- `snd (v₁, v₂) → v₂`
- `case (inl v) of ... → [x₁ ↦ v]t₁`
- `case (inr v) of ... → [x₂ ↦ v]t₂`
- etc.

**Why Progress still holds**: Every well-typed ADT term is either a value or can take a step.

### Preservation Theorem

**Theorem**: If `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`.

**Extension to ADTs**: Each new reduction rule preserves types:

**Example - fst reduction**:
```
If    Γ ⊢ fst (v₁, v₂) : τ₁
Then  Γ ⊢ v₁ : τ₁
```

Why? Because `(v₁, v₂) : τ₁ × τ₂` means `v₁ : τ₁`, and `fst` extracts the first component.

**Example - case reduction**:
```
If    Γ ⊢ case (inl v) of inl x => t₁ | inr y => t₂ : τ
And   case (inl v) of ... → [x ↦ v]t₁
Then  Γ ⊢ [x ↦ v]t₁ : τ
```

Why? Because the typing rule for case ensures `Γ, x:τ₁ ⊢ t₁ : τ`, and substitution preserves types.

### Strong Normalization

**Theorem**: All well-typed terms in STLC + ADTs terminate.

**Why?** ADTs don't add general recursion:
- Products combine finite terms → finite
- Sums choose between finite terms → finite
- Pattern matching extracts from finite terms → finite
- Lists are finite (we don't have fix yet!)

STLC + ADTs is still **not Turing-complete** - we still can't write infinite loops!

---

## Part 9: Common Patterns in Practice

### Pattern 1: Option/Maybe (Null Safety)

```
Option τ = Unit + τ

none : Option τ = inl[τ] ()
some : τ → Option τ = λx:τ. inr[Unit] x

mapOption : (τ₁ → τ₂) → Option τ₁ → Option τ₂
bindOption : Option τ₁ → (τ₁ → Option τ₂) → Option τ₂
getOrElse : Option τ → τ → τ
```

**Use case**: Representing values that might not exist

### Pattern 2: Either/Result (Error Handling)

```
Either τ₁ τ₂ = τ₁ + τ₂

left : τ₁ → Either τ₁ τ₂ = λx:τ₁. inl[τ₂] x
right : τ₂ → Either τ₁ τ₂ = λx:τ₂. inr[τ₁] x

Result τ = Either Bool τ  // Bool represents error, τ represents success
```

**Use case**: Operations that can fail with error information

### Pattern 3: Binary Trees

```
Tree τ = <leaf:Unit, node:{value:τ, left:Tree τ, right:Tree τ}>

leaf : Tree τ = <leaf=()> as Tree τ

node : τ → Tree τ → Tree τ → Tree τ
node = λv:τ. λl:Tree τ. λr:Tree τ.
  <node={value=v, left=l, right=r}> as Tree τ

height : Tree τ → Nat
height = λt:Tree τ.
  case t of
    <leaf=u> => 0
  | <node=n> => succ (max (height n.left) (height n.right))
```

**Use case**: Hierarchical data structures

### Pattern 4: State Machines

```
State = <idle:Unit,
         loading:Nat,
         ready:{data:Nat},
         error:Bool>

transition : State → State
transition = λs:State.
  case s of
    <idle=u> => <loading=0> as State
  | <loading=progress> =>
      if iszero progress
        then <error=true> as State
        else <ready={data=progress}> as State
  | <ready=d> => <idle=()> as State
  | <error=critical> => <idle=()> as State
```

**Use case**: Modeling application state and transitions

---

## Part 10: Putting It All Together

### Complete Example: Expression Evaluator

Let's build a simple arithmetic expression language!

**Step 1**: Define the expression type
```
Expr = <lit:Nat,
        add:{left:Expr, right:Expr},
        mul:{left:Expr, right:Expr}>
```

**Step 2**: Define constructors
```
lit : Nat → Expr
lit = λn:Nat. <lit=n> as Expr

add : Expr → Expr → Expr
add = λl:Expr. λr:Expr. <add={left=l, right=r}> as Expr

mul : Expr → Expr → Expr
mul = λl:Expr. λr:Expr. <mul={left=l, right=r}> as Expr
```

**Step 3**: Define evaluator
```
eval : Expr → Nat
eval = λe:Expr.
  case e of
    <lit=n> => n
  | <add=pair> => plus (eval pair.left) (eval pair.right)
  | <mul=pair> => mult (eval pair.left) (eval pair.right)
```

**Step 4**: Use it!
```
-- Represent: (2 + 3) * 4
let expr = mul (add (lit 2) (lit 3)) (lit 4)

eval expr
→  (evaluates to 20)
```

### What You've Learned

You now understand:
- ✓ Product types for combining values
- ✓ Sum types for choosing alternatives
- ✓ Pattern matching for extracting data
- ✓ Records for named fields
- ✓ Variants for tagged unions
- ✓ Lists and recursive data structures
- ✓ Common patterns: Option, Either, Trees
- ✓ How ADTs maintain type safety

### Next Steps

**Ready for exercises?** Go to `exercises/EXERCISES.md` and implement:
- List operations (append, reverse, map, fold)
- Binary tree operations (height, mirror, traversal)
- Option/Either utilities
- Expression evaluators with optimization

**Need more practice?** Use the REPL to experiment:
```bash
cd chapter-03-stlc-adt
stack run
```

**Ready for Chapter 4?** Learn how to write these programs WITHOUT type annotations through type inference!
