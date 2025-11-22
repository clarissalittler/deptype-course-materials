# Chapter 5: System F - Common Mistakes and How to Avoid Them

## Introduction

System F adds explicit polymorphism to lambda calculus, and while the concepts are elegant, students consistently make the same mistakes. This guide identifies these pitfalls and shows you how to avoid them.

**Use this guide**:
- When type checking fails mysteriously
- When your REPL gives unexpected errors
- When derivations don't work out
- When implementing Church encodings
- As a reference while doing exercises

---

## Mistake #1: Forgetting Type Applications (THE MOST COMMON!)

### The Mistake

**Problem**: Writing `id true` instead of `id [Bool] true`

**Wrong**:
```
id : ∀α. α → α
id true   ❌ WRONG!
```

**Why it's wrong**: `id` has type `∀α. α → α`, not `Bool → Bool`. You must apply it to a type first!

### How to Recognize It

You'll see type errors like:
```
Expected: τ₁ → τ₂
Found: ∀α. τ
```

Or:
```
Cannot apply polymorphic function without type argument
```

### How to Fix It

**Always apply types to polymorphic functions before applying terms:**

```
id [Bool] true   ✓ CORRECT

Step by step:
1. id : ∀α. α → α
2. id [Bool] : Bool → Bool      (type application)
3. id [Bool] true : Bool        (term application)
```

### Examples

**Wrong:**
```
const x y                        ❌
map f list                       ❌
pair 5 true                      ❌
```

**Correct:**
```
const [Nat] [Bool] x y           ✓
map [Nat] [Bool] f list          ✓
pair [Nat] [Bool] 5 true         ✓
```

### Detection Strategy

Before every application `f t`:
1. Check the type of f
2. If it's `∀α. τ`, you need type application: `f [τ'] t`
3. Keep applying types until you have a function type `τ₁ → τ₂`
4. Then apply terms

### Practice Problems

Fix these (answers below):
1. `id 42`
2. `const "hello" 100`
3. `twice succ 0`

<details>
<summary>Answers</summary>

1. `id [Nat] 42` (or `id [Int] 42` depending on type system)
2. `const [String] [Nat] "hello" 100`
3. `twice [Nat] succ 0` (assuming `twice : ∀α. (α→α) → α → α`)
</details>

---

## Mistake #2: Confusing Λ and λ

### The Mistake

**Problem**: Using λ for type abstraction or Λ for term abstraction

**Wrong**:
```
λα. λx:α. x        ❌ (λ cannot bind type variables!)
Λx:Nat. x          ❌ (Λ cannot bind term variables!)
```

**Why it's wrong**: They're completely different constructs:
- `λx:τ. t` - term abstraction (function)
- `Λα. t` - type abstraction (polymorphic function)

### How to Recognize It

You'll see parse errors or type errors like:
```
Expected type variable after Λ, found term variable
Expected term variable after λ, found type variable
```

### How to Fix It

**Remember the pattern:**
```
Λ (capital) - Type variables (α, β, γ)
λ (lowercase) - term variables (x, y, z)
```

**Correct examples:**
```
Λα. λx:α. x                    ✓ Type var α, term var x
Λα. Λβ. λx:α. λy:β. x          ✓ Type vars α, β, term vars x, y
λf:∀α. α→α. f [Bool] true      ✓ Term var f with polymorphic type
```

### Mnemonic

**"Capital Λ for Types, lowercase λ for terms"**
- Type variables are often capital letters (A, B, C) or Greek (α, β, γ)
- Term variables are often lowercase (x, y, z)

---

## Mistake #3: Type Variables Not in Scope

### The Mistake

**Problem**: Using type variables that aren't bound by ∀ or Λ

**Wrong**:
```
λx:α. x            ❌ (Where does α come from?)
x : α              ❌ (α not in Δ!)
```

**Why it's wrong**: Type variables must be introduced by either:
- `∀α` in a type
- `Λα` in a term
- Added to context Δ during type checking

### How to Recognize It

You'll see errors like:
```
Type variable α not in scope
Unbound type variable: α
```

### How to Fix It

**Every type variable must be bound:**

```
∀α. α → α                      ✓ α bound by ∀
Λα. λx:α. x                    ✓ α bound by Λ
λx:∀α. α → α. ...              ✓ α bound inside the type
```

**Wrong:**
```
λx:α. x                        ❌ α not bound

Should be:
Λα. λx:α. x                    ✓
```

### In Type Derivations

When building typing derivations:
```
α; ⊢ λx:α. x : α → α           ✓ α in Δ

⊢ λx:α. x : α → α              ❌ α not in Δ
```

### Detection Strategy

Before using a type variable α:
1. Check if α ∈ Δ (in type checking)
2. Check if α is bound by ∀ or Λ (in syntax)
3. If not, add a Λα or ∀α

---

## Mistake #4: Wrong Order of Type/Term Abstractions

### The Mistake

**Problem**: Putting Λ after λ instead of before

**Wrong**:
```
λx:α. Λα. x        ❌
```

**Why it's wrong**: The type variable α is used in `λx:α` before it's introduced by `Λα`!

### How to Recognize It

You'll see errors like:
```
Type variable α used before being bound
α not in scope in type annotation
```

### How to Fix It

**Type abstractions (Λ) must come before term abstractions (λ) that use those types:**

```
Λα. λx:α. x        ✓ α introduced before use

Order:
1. Λα               (introduce type)
2. λx:α             (use that type)
```

**More examples:**
```
Λα. Λβ. λx:α. λy:β. x              ✓ Types before terms
Λα. λx:α. Λβ. λy:β. x              ✓ But β must come before y
λx:α. Λα. x                        ❌ α used before introduced
```

### General Pattern

```
Λα₁. Λα₂. ... Λαₙ. λx₁:τ₁. λx₂:τ₂. ... λxₘ:τₘ. t
└─────────────────┘ └─────────────────────────────┘
  Type abstractions        Term abstractions
```

---

## Mistake #5: Incorrect Type Substitution

### The Mistake

**Problem**: Not substituting types correctly in T-TyApp

**Wrong**:
```
(Λα. λx:α. succ x) [Bool]
→ λx:Bool. succ [Bool] x   ❌ (succ doesn't take type argument!)
```

**Why it's wrong**: Type substitution only replaces type variables (α), not term-level operations!

### How to Recognize It

Results that don't make sense, or type errors after "correct" substitution.

### How to Fix It

**Type substitution [α ↦ τ]t only replaces occurrences of the type variable α:**

```
[α ↦ Bool](λx:α. x)
= λx:Bool. x                       ✓

[α ↦ Bool](λx:α. succ x)
= λx:Bool. succ x                  ✓ (succ unchanged!)

[α ↦ Bool](λx:α. λy:α. x)
= λx:Bool. λy:Bool. x              ✓ (all α replaced)
```

### Substitution Rules

1. Replace type variables: `[α ↦ τ]α = τ`
2. Recurse into types: `[α ↦ τ](σ₁ → σ₂) = ([α ↦ τ]σ₁) → ([α ↦ τ]σ₂)`
3. Don't touch term variables: `[α ↦ τ]x = x`
4. Don't touch term constants: `[α ↦ τ]true = true`
5. Recurse into terms: `[α ↦ τ](t₁ t₂) = ([α ↦ τ]t₁) ([α ↦ τ]t₂)`

---

## Mistake #6: Incorrect Church Encodings

### The Mistake

**Problem**: Forgetting type abstractions or applications in Church encodings

**Wrong**:
```
true = λt. λf. t                   ❌ Missing Λα!
```

**Why it's wrong**: Church encodings in System F require ∀ to be polymorphic over the result type.

### How to Recognize It

Type errors when trying to use Church-encoded values in different contexts.

### How to Fix It

**Church encodings always start with type abstraction:**

**Booleans:**
```
CBool = ∀α. α → α → α

true  = Λα. λt:α. λf:α. t          ✓
false = Λα. λt:α. λf:α. f          ✓
```

**Natural Numbers:**
```
CNat = ∀α. (α → α) → α → α

zero = Λα. λf:α→α. λx:α. x         ✓
one  = Λα. λf:α→α. λx:α. f x       ✓
```

**Using them requires type application:**
```
true [Nat] 5 0                     ✓
zero [Nat] succ 0                  ✓
```

### Common Encoding Mistakes

**Wrong: Forgetting Λ**
```
succ = λn:CNat. λf. λx. f (n f x)  ❌
```

**Correct:**
```
succ = λn:CNat. Λα. λf:α→α. λx:α. f (n [α] f x)  ✓
```

**Wrong: Forgetting type application on n**
```
succ = λn:CNat. Λα. λf:α→α. λx:α. f (n f x)  ❌
```

**Correct:**
```
succ = λn:CNat. Λα. λf:α→α. λx:α. f (n [α] f x)  ✓
                                       └─┘
                                    Apply n to type α first!
```

---

## Mistake #7: Mixing Up ∀ and Λ

### The Mistake

**Problem**: Using ∀ in terms or Λ in types

**Wrong**:
```
∀α. λx:α. x        ❌ (∀ is not a term constructor!)
Λα. α → α          ❌ (Λ is not a type constructor!)
```

**Why it's wrong**:
- `∀α. τ` is a TYPE (used in type annotations)
- `Λα. t` is a TERM (used in expressions)

### How to Recognize It

Parse errors or nonsensical expressions.

### How to Fix It

**Remember the contexts:**

**In types (right side of `:`):**
```
∀α. α → α          ✓ Universal type
∀α. ∀β. α → β → α  ✓ Multiple quantifiers
```

**In terms (expressions):**
```
Λα. λx:α. x        ✓ Type abstraction
Λα. Λβ. λx:α. x    ✓ Multiple type abstractions
```

**In annotations:**
```
id : ∀α. α → α     ✓ Type uses ∀
id = Λα. λx:α. x   ✓ Term uses Λ
```

### Side-by-Side Comparison

```
Type:  ∀α. α → α
Term:  Λα. λx:α. x
       ↑
       Corresponds but different syntax!
```

---

## Mistake #8: Parametricity Violations

### The Mistake

**Problem**: Trying to inspect or create values of polymorphic type

**Wrong conceptually** (not actually expressible in System F):
```
-- Cannot inspect type
f : ∀α. α → String
f = Λα. λx:α. if (α == Nat) then "number" else "other"  ❌

-- Cannot create values of unknown type
g : ∀α. Unit → α
g = Λα. λu:Unit. 0  ❌ (what if α = Bool?)
```

**Why it's wrong**: Parametricity means polymorphic functions work uniformly for all types - they can't inspect types or create values.

### How to Recognize It

These mistakes are usually caught at a conceptual level - System F won't let you write them!

You might try to do something like:
```
f : ∀α. α → α
f = Λα. λx:α. x + 1  ❌ (α might not support +!)
```

### How to Fix It

**Only do operations that work for ALL types:**

**Identity is OK:**
```
f : ∀α. α → α
f = Λα. λx:α. x      ✓ (works for all α)
```

**Duplication is OK:**
```
dup : ∀α. α → Pair α α
dup = Λα. λx:α. pair [α] [α] x x  ✓
```

**Type-specific operations need the type to be concrete:**
```
incNat : Nat → Nat
incNat = λx:Nat. succ x            ✓ (Nat is concrete)
```

### Free Theorem Violations

If you find yourself writing:
- `∀α. α → β` where β is concrete and α is not - probably wrong (can't create β from unknown α)
- `∀α. α → α` that does more than return input - impossible (parametricity theorem!)
- Polymorphic function that uses type-specific operations - wrong (breaks parametricity)

---

## Mistake #9: Incorrect Existential Encoding

### The Mistake

**Problem**: Wrong encoding of existential types

**Wrong**:
```
∃α. τ = ∀α. τ      ❌
```

**Why it's wrong**: Existentials hide the type, but this doesn't capture that!

### How to Recognize It

Type checking fails when trying to use the encoding, or the abstraction doesn't work.

### How to Fix It

**Correct encoding:**
```
∃α. τ ≡ ∀R. (∀α. τ → R) → R  ✓
```

**Reading:** "To get an R, you must provide a function that works for ANY type α"

**Example:**
```
Counter = ∃State. {
  new  : State,
  inc  : State → State,
  get  : State → Nat
}

Expands to:
Counter = ∀R. (∀State. {new:State, inc:State→State, get:State→Nat} → R) → R
```

### Pack and Unpack

**Pack (create existential):**
```
pack [Nat] {new = 0, inc = succ, get = id}
: ∃State. {new:State, inc:State→State, get:State→Nat}
```

**Unpack (use existential):**
```
unpack counter as (State, ops) in
  ops.get (ops.inc ops.new)
```

---

## Mistake #10: Forgetting Strong Normalization

### The Mistake

**Problem**: Trying to write infinite loops or general recursion

**Wrong:**
```
loop : ∀α. α
loop = Λα. loop [α]    ❌ (won't type check!)
```

**Why it's wrong**: System F has strong normalization - all well-typed programs terminate!

### How to Recognize It

You can't actually make this mistake in System F - the type system prevents it!

But conceptually, students try to write:
- Infinite loops
- General recursion without fixed-point combinator
- Non-terminating functions

### How to Fix It

**Remember: System F is NOT Turing-complete!**

You cannot write:
```
while true do ...          ❌
loop forever              ❌
fact n = fact (n-1)       ❌ (without fix)
```

To get general recursion, you need:
1. Add a primitive fixed-point combinator (like in ML)
2. Move to a system with recursive types
3. Use the encoding with recursive types (Chapter 6+)

**For this chapter:** Focus on terminating programs!

---

## Mistake #11: Confusing HM and System F Polymorphism

### The Mistake

**Problem**: Expecting HM-style inference or let-polymorphism

**Wrong expectations:**
```
-- In HM: This works!
let id = λx. x in (id 1, id true)  ✓

-- In System F: Must be explicit!
let id = Λα. λx:α. x in
  (id [Nat] 1, id [Bool] true)     ✓
```

**Why it's different**:
- HM: Implicit polymorphism, decidable inference
- System F: Explicit polymorphism, undecidable inference

### How to Recognize It

You expect types to be inferred but get errors asking for annotations.

### How to Fix It

**Remember the differences:**

| Feature | Hindley-Milner | System F |
|---------|----------------|----------|
| Type abstraction | Implicit | Explicit (Λα) |
| Type application | Implicit | Explicit ([τ]) |
| First-class poly | No | Yes |
| Inference | Decidable | Undecidable |

**In System F, be explicit about everything!**

---

## Debugging Checklist

When something doesn't work, check:

1. **Type applications:**
   - [ ] Did you apply all necessary type arguments?
   - [ ] Are type applications before term applications?

2. **Type/Term distinction:**
   - [ ] Using Λ for types, λ for terms?
   - [ ] Using ∀ in types, Λ in terms?

3. **Variable scope:**
   - [ ] Are all type variables in Δ?
   - [ ] Are all term variables in Γ?
   - [ ] Is Λα before any use of α in types?

4. **Church encodings:**
   - [ ] Starting with Λα?
   - [ ] Applying type arguments when using encoded values?

5. **Substitution:**
   - [ ] Only replacing type variables in type substitution?
   - [ ] Handling variable capture correctly?

6. **Contexts:**
   - [ ] Updating Δ when adding Λα?
   - [ ] Updating Γ when adding λx:τ?

---

## Practice Corrections

Find the mistakes in each example:

### Example 1
```
wrong_id = λx:α. x
```

<details>
<summary>Answer</summary>
α is not bound! Should be: `Λα. λx:α. x`
</details>

### Example 2
```
wrong_const = Λα. Λβ. λx:α. λy:β. x
wrong_use = wrong_const 5 true
```

<details>
<summary>Answer</summary>
Missing type applications! Should be: `wrong_const [Nat] [Bool] 5 true`
</details>

### Example 3
```
wrong_true = λt. λf. t
```

<details>
<summary>Answer</summary>
Missing type abstraction! Should be: `Λα. λt:α. λf:α. t`
</details>

### Example 4
```
wrong_succ = λn:CNat. Λα. λf:α→α. λx:α. f (n f x)
```

<details>
<summary>Answer</summary>
Missing type application on n! Should be: `f (n [α] f x)`
</details>

### Example 5
```
wrong_type : α → α
wrong_type = Λα. λx:α. x
```

<details>
<summary>Answer</summary>
Type is missing ∀! Should be: `wrong_type : ∀α. α → α`
</details>

---

## Summary of Key Points

1. **Always use type applications** - `id [Bool] true`, not `id true`
2. **Λ for types, λ for terms** - Don't mix them up!
3. **Type variables must be in scope** - Bound by ∀ or Λ
4. **Type abstractions before term abstractions** - `Λα. λx:α`, not `λx:α. Λα`
5. **Type substitution only replaces types** - Terms are unchanged
6. **Church encodings need Λα** - Always start with type abstraction
7. **∀ in types, Λ in terms** - Different contexts
8. **Respect parametricity** - Can't inspect or create polymorphic values
9. **Correct existential encoding** - `∃α. τ ≡ ∀R. (∀α. τ → R) → R`
10. **System F always terminates** - No infinite loops allowed!
11. **Be explicit** - Unlike HM, everything must be annotated

---

## When You're Still Stuck

1. **Review TUTORIAL.md** - Step-by-step examples
2. **Check CHEAT_SHEET.md** - Quick reference
3. **Use the REPL** - Test your understanding
4. **Draw derivation trees** - Visualize type checking
5. **Compare with working examples** - See what's different
6. **Ask for help** - Don't struggle alone!

Remember: System F is more verbose than HM, but that explicitness gives you first-class polymorphism and deeper understanding!
