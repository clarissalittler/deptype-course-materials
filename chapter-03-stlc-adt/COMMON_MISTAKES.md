# Chapter 3: Common Mistakes and How to Avoid Them

## Introduction

Algebraic Data Types add significant expressiveness to STLC, but they also introduce new ways to make mistakes. This guide helps you avoid common pitfalls when working with products, sums, records, variants, lists, and pattern matching.

**Use this guide**:
- When type checking fails unexpectedly
- When pattern matches don't work as expected
- When exercise tests fail
- As a reference while implementing ADT operations

---

## Mistake #1: Forgetting Type Annotations on Sums

### The Mistake

**Wrong**:
```
inl true   ❌
inr 0      ❌
```

**Correct**:
```
inl[Nat] true : Bool + Nat   ✓
inr[Bool] 0 : Bool + Nat     ✓
```

### Why It Happens

With products, the type is clear from both components:
```
(true, 0) : Bool × Nat   // Type checker sees both Bool and Nat
```

But with sums, only ONE alternative is present:
```
inl true : Bool + ???   // Type checker doesn't know the other type!
```

### How to Fix

**Always annotate the "other" type**:
```
inl[τ₂] t : τ₁ + τ₂   // When t : τ₁
inr[τ₁] t : τ₁ + τ₂   // When t : τ₂
```

### Practice

Fix these terms:
1. `inl false` intended type `Bool + Nat`
2. `inr 5` intended type `Bool + Nat`

<details>
<summary>Answers</summary>

1. `inl[Nat] false : Bool + Nat`
2. `inr[Bool] 5 : Bool + Nat`
</details>

---

## Mistake #2: Case Branches with Different Types

### The Mistake

**Wrong**:
```
case x of
  inl b => b        : Bool
| inr n => n        : Nat
❌ TYPE ERROR! Branches return different types
```

**Correct**:
```
case x of
  inl b => b           : Bool
| inr n => iszero n    : Bool
✓ Both branches return Bool
```

### Why It Matters

What type should the whole expression have?
```
let result = case x of inl b => b | inr n => n

What is the type of result?
- If x is inl, result is Bool
- If x is inr, result is Nat
- The type can't be both!
```

### The Rule

```
Γ ⊢ t : τ₁ + τ₂
Γ, x₁:τ₁ ⊢ t₁ : τ      ← Both branches must
Γ, x₂:τ₂ ⊢ t₂ : τ      ← return the same type τ
────────────────────────────────────────────
Γ ⊢ case t of inl x₁ => t₁ | inr x₂ => t₂ : τ
```

### How to Fix

Make both branches return the same type:

**Example 1**: Convert both to Bool
```
case x of
  inl b => b
| inr n => iszero n
```

**Example 2**: Convert both to a sum type
```
case x of
  inl b => inl[Nat] b
| inr n => inr[Bool] n
```

### Practice

Fix this case expression for type `Bool + Nat`:
```
case opt of
  inl b => b
| inr n => succ n
```

<details>
<summary>Answer</summary>

Make both branches return the same type. Options:
1. Return Bool: `case opt of inl b => b | inr n => iszero n`
2. Return Nat: `case opt of inl b => if b then 0 else 1 | inr n => succ n`
3. Return the sum back: `case opt of inl b => inl[Nat] b | inr n => inr[Bool] (succ n)`
</details>

---

## Mistake #3: Non-Exhaustive Pattern Matching

### The Mistake

**Wrong**:
```
match xs with
  x::rest => ...
❌ MISSING CASE! What about empty list []?
```

**Correct**:
```
match xs with
  [] => ...
| x::rest => ...
✓ Handles both constructors
```

### Why It's Dangerous

Non-exhaustive patterns can fail at runtime:
```
// In a language without exhaustiveness checking
match xs with
  x::rest => process x

// If xs is [], this crashes!
```

### How to Detect

**For each type, know its constructors**:

| Type | Constructors | Pattern Match Needs |
|------|--------------|---------------------|
| `τ₁ + τ₂` | `inl`, `inr` | Both `inl x =>` and `inr y =>` |
| `List τ` | `[]`, `::` | Both `[] =>` and `x::xs =>` |
| `<l₁:τ₁, l₂:τ₂>` | `<l₁=...>`, `<l₂=...>` | Cases for both `l₁` and `l₂` |

### Common Patterns

**Exhaustive** ✓:
```
// Sum type
case opt of
  inl u => ...
| inr x => ...

// List
match xs with
  [] => ...
| x::rest => ...

// Variant
case shape of
  <circle=r> => ...
| <square=s> => ...
| <rectangle=dims> => ...
```

**Non-exhaustive** ✗:
```
// Missing inr case
case opt of
  inl u => ...

// Missing [] case
match xs with
  x::rest => ...

// Missing circle case
case shape of
  <square=s> => ...
| <rectangle=dims> => ...
```

### How to Fix

**List all constructors** before writing your match:
1. Identify the type being matched
2. List all its constructors
3. Write a case for each one
4. Verify you haven't missed any

### Practice

Are these exhaustive?
1. `match xs with [] => 0`
2. `case v of <left=x> => x | <right=y> => y`
3. `case pair of (x, y) => x`

<details>
<summary>Answers</summary>

1. **Non-exhaustive** ✗ - Missing `x::xs` case
2. **Exhaustive** ✓ - If variant type has only `left` and `right`
3. **Exhaustive** ✓ - Pairs have only one constructor `(_, _)`
</details>

---

## Mistake #4: Confusing Products and Sums

### The Mistake

**Wrong thinking**:
```
"I want to represent a value that's either Bool OR Nat"
→ Uses: (Bool, Nat)   ❌

"I want to combine Bool AND Nat"
→ Uses: Bool + Nat    ❌
```

**Correct**:
```
"Either Bool OR Nat" → Bool + Nat   ✓ (sum)
"Bool AND Nat"       → Bool × Nat   ✓ (product)
```

### The Distinction

**Product (×)**: ALL values together
- Pair: `(true, 0)` contains BOTH true AND 0
- Record: `{x=0, y=1}` has BOTH x AND y fields
- Think: struct, object, tuple

**Sum (+)**: ONE value from alternatives
- `inl[Nat] true` contains true OR a Nat (chose Bool)
- `inr[Bool] 0` contains a Bool OR 0 (chose Nat)
- Think: enum, union, variant

### Visual Aid

**Product**: You have ALL the pieces
```
(true, 0, "hello") : Bool × Nat × String
 ^^^^  ^   ^^^^^^^
  All three values are present
```

**Sum**: You have ONE of the options
```
<circle=5> as <circle:Nat, square:Nat, rectangle:Record>
 ^^^^^^^^^
  Only circle is present (not square or rectangle)
```

### How to Choose

**Use Product when**:
- You need all values together
- Example: Point has both x AND y coordinates
- Example: Person has name AND age AND email

**Use Sum when**:
- You need one of several alternatives
- Example: Optional value is either None OR Some value
- Example: Result is either Error OR Success
- Example: Shape is Circle OR Square OR Rectangle

### Practice

Choose product or sum:
1. Representing a 2D point (x, y)
2. Representing an optional value (might not exist)
3. Representing a login state (logged in with user info, or logged out)

<details>
<summary>Answers</summary>

1. **Product** `{x:Nat, y:Nat}` - Need both coordinates
2. **Sum** `Unit + τ` (Option) - Either nothing or a value
3. **Sum** `<loggedOut:Unit, loggedIn:{user:String, ...}>` - One state at a time
</details>

---

## Mistake #5: Not Understanding Pattern Variable Scope

### The Mistake

**Wrong thinking**:
```
match xs with
  [] => x      ❌ Where does x come from?
| x::rest => x
```

The `x` in the `[]` case is not bound!

**Correct**:
```
match xs with
  [] => 0           ✓ Use a default value
| x::rest => x      ✓ x is bound in this case only
```

### The Rule

Pattern variables are only in scope in their branch:
```
match xs with
  [] => t₁           // No variables bound here
| x::rest => t₂      // x and rest available in t₂ only
```

### Visualization

```
match xs with
  ┌── [] => ...       // x not in scope
  └── x::rest => ...  // x in scope only here
                      // rest in scope only here
```

### Common Variations

**Case expressions**:
```
case opt of
  inl x => x + 1    // x : τ₁, in scope only in this branch
| inr y => y - 1    // y : τ₂, in scope only in this branch
                    // x is NOT in scope here!
```

**Nested patterns**:
```
match xs with
  [] => 0
| (x, y)::rest =>   // x, y, and rest all in scope
    x + y           // can use all three
```

### How to Avoid

**Check scope before using variables**:
1. Which pattern am I in?
2. What variables does this pattern bind?
3. Am I using only those variables?

---

## Mistake #6: Misusing Records vs Variants

### The Mistake

**Confusion**: "When do I use records vs variants?"

**Wrong**:
```
// Trying to use record as variant
{x=0} : {x:Nat, y:Nat}   ❌ Missing y field!

// Trying to use variant as record
<circle=5> as Shape
shape.circle             ❌ Can't project from variant!
```

### The Distinction

**Records (Named Products)**:
- ALL fields present
- Access with projection (`.field`)
- Like structs/objects

```
{x=0, y=1} : {x:Nat, y:Nat}
point.x    // Access field directly
```

**Variants (Named Sums)**:
- ONE tag present at a time
- Access with pattern matching
- Like enums/unions

```
<circle=5> as <circle:Nat, square:Nat>
case shape of <circle=r> => ... | <square=s> => ...
```

### Visual Aid

**Record**: All fields always there
```
{name="Alice", age=30, email="..."}
 ^^^^          ^^^      ^^^^^
 All three fields present
```

**Variant**: One tag at a time
```
At time 1: <idle=()>
At time 2: <loading=50>
At time 3: <done={result:Nat}>
           ^^^^^^^^^^^^^
           Only one tag active
```

### How to Choose

**Use Records when**:
- Grouping related data
- All fields always present
- Example: Point {x, y}, Person {name, age, email}

**Use Variants when**:
- Representing alternatives
- Only one case at a time
- Example: State machine, Option, Either

### Practice

Choose record or variant:
1. User information (name, email, age)
2. Response from server (success with data, or error with message)
3. Rectangle (width and height)

<details>
<summary>Answers</summary>

1. **Record** `{name:String, email:String, age:Nat}` - All fields present
2. **Variant** `<success:{data:τ}, error:{message:String}>` - One at a time
3. **Record** `{width:Nat, height:Nat}` - Both dimensions present
</details>

---

## Mistake #7: Forgetting to Handle the Base Case in Recursive Functions

### The Mistake

**Wrong**:
```
length = λxs:List Nat.
  match xs with
    x::rest => succ (length rest)
❌ Missing base case! What about []?
```

**Correct**:
```
length = λxs:List Nat.
  match xs with
    [] => 0
  | x::rest => succ (length rest)
✓ Base case returns 0
```

### Why It's Critical

Without a base case, recursion never stops!

**Trace without base case**:
```
length (0::[])
→ match (0::[]) with x::rest => succ (length rest)
→ succ (length [])
→ succ (match [] with x::rest => succ (length rest))
→ ??? [] doesn't match x::rest, no other case!
```

### The Pattern

**Every recursive function needs**:
1. **Base case**: Handles the "smallest" input (usually `[]` for lists)
2. **Recursive case**: Handles larger inputs by breaking them down

```
recursiveFunction = λxs:List τ.
  match xs with
    [] => <base value>          // Base case
  | x::rest =>                  // Recursive case
      <combine x with (recursiveFunction rest)>
```

### Common Examples

**Length**:
- Base: Empty list has length 0
- Recursive: List has length 1 + length of tail

**Sum**:
- Base: Empty list sums to 0
- Recursive: Sum is head + sum of tail

**Append**:
- Base: Appending to [] gives the second list
- Recursive: Prepend head, append rest

### How to Avoid

**Before writing recursion**:
1. What's the base case? (usually `[]`)
2. What should it return?
3. How does the recursive case use the result?

### Practice

Add base cases:
```
reverse = λxs:List τ.
  match xs with
    x::rest => append (reverse rest) (x::[])
```

<details>
<summary>Answer</summary>

```
reverse = λxs:List τ.
  match xs with
    [] => []                                    // Base case
  | x::rest => append (reverse rest) (x::[])   // Recursive case
```
</details>

---

## Mistake #8: Wrong Option Encoding

### The Mistake

**Wrong**:
```
Option τ = Bool + τ     ❌
Option τ = τ + τ        ❌
```

**Correct**:
```
Option τ = Unit + τ     ✓
```

### Why?

**With Bool**:
```
Option τ = Bool + τ
none = inl[τ] true     // Represents absence
some = λx:τ. inr[Bool] x

// But what does inl[τ] false mean?
// We have TWO ways to represent absence!
```

**With τ + τ**:
```
Option τ = τ + τ
none = ???  // No way to represent "no value" without a value!
```

**With Unit**:
```
Option τ = Unit + τ
none = inl[τ] ()       // Unit has exactly ONE value
some = λx:τ. inr[Unit] x

// Perfect! One way to say "none", one way to say "some x"
```

### The Key Insight

We need a type with **exactly one value** to represent "nothing":
- `Unit` has one value: `()`
- `Bool` has two values: `true`, `false` (too many!)
- We don't want multiple representations of "nothing"

### Practice

Why can't we use `Option τ = Nat + τ`?

<details>
<summary>Answer</summary>

Nat has infinitely many values (0, 1, 2, ...). We'd have infinite ways to represent "none":
- `inl[τ] 0` means none?
- `inl[τ] 1` means none?
- `inl[τ] 2` means none?

This is confusing and error-prone. We want exactly ONE canonical representation of "none".
</details>

---

## Mistake #9: Incorrect Either Usage

### The Mistake

**Wrong**:
```
validateInput : String → Either String User
validateInput = λs:String.
  if valid s
    then s              ❌ Type error!
    else "Invalid"      ❌ Type error!
```

The branches return `String`, but we need `Either String User`!

**Correct**:
```
validateInput : String → Either String User
validateInput = λs:String.
  if valid s
    then inr[String] (parse s)  ✓ Returns User on right
    else inl[User] "Invalid"    ✓ Returns String on left
```

### The Pattern

Either represents "error OR success":
```
Either Error Success = Error + Success

left  : Error → Either Error Success   // For errors
right : Success → Either Error Success // For success
```

**Convention**: Errors on the left, success on the right
- "Right is right" (correct)
- "Left is wrong" (error)

### Example Usage

```
safeDivide : Nat → Nat → Either String Nat
safeDivide = λm:Nat. λn:Nat.
  if iszero n
    then inl[Nat] "Division by zero"     // Error
    else inr[String] (divide m n)        // Success
```

### How to Use Results

```
result = safeDivide 10 0

case result of
  inl err => handleError err      // err : String
| inr value => useValue value     // value : Nat
```

---

## Mistake #10: Not Using the REPL for Type Checking

### The Mistake

**Problem**: Trying to debug complex ADT types by hand

**Solution**: Use the REPL!

### REPL Features for ADTs

```bash
cd chapter-03-stlc-adt
stack run
```

**Essential commands**:

1. **Check types**:
   ```
   > :type (true, 0)
   Bool × Nat

   > :type inl[Nat] true
   Bool + Nat
   ```

2. **Step through evaluation**:
   ```
   > :step case (inl[Nat] true) of inl b => b | inr n => iszero n
   case (inl[Nat] true) of inl b => b | inr n => iszero n
   → true
   ```

3. **Test pattern matching**:
   ```
   > match (0::1::[]) with [] => 0 | x::xs => x
   0
   ```

4. **Define and reuse**:
   ```
   > :let none = inl[Nat] ()
   > :let some = λx:Nat. inr[Unit] x
   > :type some 42
   Unit + Nat
   ```

### When to Use the REPL

- **Type checking**: Verify your terms type check
- **Debugging patterns**: Test if patterns match correctly
- **Understanding evaluation**: See step-by-step reduction
- **Exploring examples**: Try variations of examples

---

## Debugging Checklist

When something goes wrong with ADTs:

**1. Sum Types**:
- [ ] Did I annotate inl/inr with the other type?
- [ ] Do both case branches return the same type?
- [ ] Am I handling both inl and inr cases?

**2. Products**:
- [ ] Am I using fst/snd correctly?
- [ ] Did I remember both components are always present?

**3. Pattern Matching**:
- [ ] Is my pattern match exhaustive?
- [ ] Are pattern variables only used in their branch?
- [ ] Did I handle the base case for recursive functions?

**4. Records vs Variants**:
- [ ] Am I using records for "all fields present"?
- [ ] Am I using variants for "one alternative"?
- [ ] Am I accessing records with `.field` and variants with `case`?

**5. Option/Either Patterns**:
- [ ] Am I using `Unit + τ` for Option?
- [ ] Am I using `inl` for errors and `inr` for success?
- [ ] Am I wrapping values with constructors (not returning raw values)?

**6. Lists**:
- [ ] Am I handling both `[]` and `::` cases?
- [ ] Do I have a base case for recursion?
- [ ] Am I building lists with `::`correctly?

**7. Type Annotations**:
- [ ] Did I annotate variant types (`as τ`)?
- [ ] Did I annotate sum injections (`inl[τ₂]`, `inr[τ₁]`)?

**8. Using Tools**:
- [ ] Have I tested in the REPL?
- [ ] Have I used `:type` to check types?
- [ ] Have I used `:step` to trace evaluation?
- [ ] Have I run the test suite?

---

## Quick Reference: Common Patterns

### Option Type
```
Option τ = Unit + τ

none : Option τ = inl[τ] ()
some : τ → Option τ = λx:τ. inr[Unit] x

getOrElse : Option τ → τ → τ
getOrElse = λopt:Option τ. λdefault:τ.
  case opt of
    inl u => default
  | inr x => x
```

### Either Type
```
Either τ₁ τ₂ = τ₁ + τ₂

left : τ₁ → Either τ₁ τ₂ = λx:τ₁. inl[τ₂] x
right : τ₂ → Either τ₁ τ₂ = λx:τ₂. inr[τ₁] x
```

### List Recursion Pattern
```
processlist : List τ → τ'
processList = λxs:List τ.
  match xs with
    [] => <base value>
  | x::rest => <combine x (processList rest)>
```

### State Machine Pattern
```
State = <state1:τ₁, state2:τ₂, ...>

transition : State → State
transition = λs:State.
  case s of
    <state1=v1> => ...
  | <state2=v2> => ...
```

---

## Summary: Top 5 Mistakes and Fixes

| # | Mistake | Fix |
|---|---------|-----|
| 1 | Missing type annotations on sums | Always write `inl[τ₂]` and `inr[τ₁]` |
| 2 | Case branches with different types | Make both branches return the same type |
| 3 | Non-exhaustive patterns | Handle ALL constructors |
| 4 | Confusing products and sums | Products = AND (all), Sums = OR (one) |
| 5 | Missing base case in recursion | Always handle `[]` for lists |

**Remember**: ADTs are powerful but require precision. Type check frequently, use the REPL, and ensure your patterns are exhaustive!

---

## What's Next?

- Review these mistakes periodically
- Keep this guide handy while doing exercises
- When tests fail, check this list first
- Use the REPL to verify your understanding
- Focus especially on pattern matching exhaustiveness

**Ready to practice?** Head to `exercises/EXERCISES.md` and test your knowledge with real implementations!
