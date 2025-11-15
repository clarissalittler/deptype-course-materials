# Chapter 3: STLC with Algebraic Data Types

## Overview

This chapter extends the Simply Typed Lambda Calculus from Chapter 2 with **algebraic data types** (ADTs), greatly increasing the language's expressiveness while maintaining type safety and strong normalization.

Algebraic data types allow us to build complex data structures from simpler ones using two key operations:
- **Product types** (×): combine multiple values (like tuples/records)
- **Sum types** (+): choose between alternatives (like unions/variants)

## Syntax Extensions

### Types

```
τ ::= ... (types from Chapter 2)
    | Unit              unit type
    | τ × τ             product type (pair)
    | τ + τ             sum type (disjoint union)
    | {l₁:τ₁,...,lₙ:τₙ}  record type
    | <l₁:τ₁,...,lₙ:τₙ>  variant type
    | List τ            list type
```

### Terms

```
t ::= ... (terms from Chapter 2)
    -- Unit
    | ()                unit value

    -- Products
    | (t, t)            pair
    | fst t             first projection
    | snd t             second projection

    -- Sums
    | inl[τ] t          left injection
    | inr[τ] t          right injection
    | case t of         case analysis
        inl x₁ => t₁
      | inr x₂ => t₂

    -- Records
    | {l₁=t₁,...,lₙ=tₙ}  record
    | t.l               projection

    -- Variants
    | <l=t> as τ        tagged value
    | case t of         variant case
        <l₁=x₁> => t₁
      | ...
      | <lₙ=xₙ> => tₙ

    -- Lists
    | []                empty list
    | t::ts             cons
    | isnil t           nil test
    | head t            list head
    | tail t            list tail

    -- Pattern Matching
    | match t with      pattern match
        p₁ => t₁
      | ...
      | pₙ => tₙ
```

### Patterns

```
p ::=
    | x                 variable
    | _                 wildcard
    | ()                unit
    | true | false      booleans
    | 0 | succ p        naturals
    | (p, p)            pair
    | inl p | inr p     sum
    | <l=p>             variant
    | [] | p::ps        list
```

### Values

```
v ::= ... (values from Chapter 2)
    | ()                unit value
    | (v, v)            pair value
    | inl[τ] v          left injection value
    | inr[τ] v          right injection value
    | {l₁=v₁,...,lₙ=vₙ}  record value
    | <l=v> as τ        variant value
    | []                nil value
    | v::vs             cons value
```

## Type System

### Unit Type

```
───────────── (T-Unit)
Γ ⊢ () : Unit
```

### Product Types

```
Γ ⊢ t₁ : τ₁    Γ ⊢ t₂ : τ₂
─────────────────────────── (T-Pair)
Γ ⊢ (t₁, t₂) : τ₁ × τ₂


Γ ⊢ t : τ₁ × τ₂
─────────────── (T-Fst)
Γ ⊢ fst t : τ₁


Γ ⊢ t : τ₁ × τ₂
─────────────── (T-Snd)
Γ ⊢ snd t : τ₂
```

### Sum Types

```
Γ ⊢ t : τ₁
─────────────────────── (T-Inl)
Γ ⊢ inl[τ₂] t : τ₁ + τ₂


Γ ⊢ t : τ₂
─────────────────────── (T-Inr)
Γ ⊢ inr[τ₁] t : τ₁ + τ₂


Γ ⊢ t : τ₁ + τ₂    Γ, x₁:τ₁ ⊢ t₁ : τ    Γ, x₂:τ₂ ⊢ t₂ : τ
────────────────────────────────────────────────────────── (T-Case)
Γ ⊢ case t of inl x₁ => t₁ | inr x₂ => t₂ : τ
```

### Record Types

```
∀i. Γ ⊢ tᵢ : τᵢ
────────────────────────────────── (T-Record)
Γ ⊢ {l₁=t₁,...,lₙ=tₙ} : {l₁:τ₁,...,lₙ:τₙ}


Γ ⊢ t : {l₁:τ₁,...,lⱼ:τⱼ,...,lₙ:τₙ}
────────────────────────────────── (T-Proj)
Γ ⊢ t.lⱼ : τⱼ
```

### Variant Types

```
Γ ⊢ t : τⱼ
─────────────────────────────────────────── (T-Tag)
Γ ⊢ <lⱼ=t> as <l₁:τ₁,...,lⱼ:τⱼ,...,lₙ:τₙ> : <l₁:τ₁,...,lₙ:τₙ>


Γ ⊢ t : <l₁:τ₁,...,lₙ:τₙ>    ∀i. Γ, xᵢ:τᵢ ⊢ tᵢ : τ
────────────────────────────────────────────────────── (T-CaseVariant)
Γ ⊢ case t of <l₁=x₁> => t₁ | ... | <lₙ=xₙ> => tₙ : τ
```

### List Types

```
────────────────── (T-Nil)
Γ ⊢ [] : List τ


Γ ⊢ t : τ    Γ ⊢ ts : List τ
─────────────────────────── (T-Cons)
Γ ⊢ t::ts : List τ


Γ ⊢ t : List τ
────────────── (T-IsNil)
Γ ⊢ isnil t : Bool


Γ ⊢ t : List τ
────────────── (T-Head)
Γ ⊢ head t : τ


Γ ⊢ t : List τ
─────────────────── (T-Tail)
Γ ⊢ tail t : List τ
```

## Operational Semantics

### Products

```
       t₁ → t₁'
──────────────────── (E-Pair1)
(t₁, t₂) → (t₁', t₂)


       t₂ → t₂'
──────────────────── (E-Pair2)
(v₁, t₂) → (v₁, t₂')


──────────────── (E-FstPair)
fst (v₁, v₂) → v₁


──────────────── (E-SndPair)
snd (v₁, v₂) → v₂


  t → t'
─────────── (E-Fst)
fst t → fst t'


  t → t'
─────────── (E-Snd)
snd t → snd t'
```

### Sums

```
      t → t'
──────────────────── (E-Inl)
inl[τ] t → inl[τ] t'


      t → t'
──────────────────── (E-Inr)
inr[τ] t → inr[τ] t'


──────────────────────────────────── (E-CaseInl)
case inl[τ₂] v of inl x₁ => t₁ | inr x₂ => t₂ → [x₁ ↦ v]t₁


──────────────────────────────────── (E-CaseInr)
case inr[τ₁] v of inl x₁ => t₁ | inr x₂ => t₂ → [x₂ ↦ v]t₂


                    t → t'
──────────────────────────────────────────────── (E-Case)
case t of inl x₁ => t₁ | inr x₂ => t₂ → case t' of inl x₁ => t₁ | inr x₂ => t₂
```

### Records

```
         tᵢ → tᵢ'
────────────────────────────────────── (E-Record)
{..., lᵢ=tᵢ, ...} → {..., lᵢ=tᵢ', ...}


────────────────────────────────── (E-ProjRecord)
{..., lⱼ=vⱼ, ...}.lⱼ → vⱼ


      t → t'
──────────────── (E-Proj)
t.l → t'.l
```

### Lists

```
     t → t'
──────────────── (E-Cons1)
t::ts → t'::ts


     ts → ts'
──────────────── (E-Cons2)
v::ts → v::ts'


────────────── (E-IsNilNil)
isnil [] → true


────────────────── (E-IsNilCons)
isnil (v::vs) → false


────────────── (E-HeadCons)
head (v::vs) → v


────────────── (E-TailCons)
tail (v::vs) → vs
```

### Pattern Matching

```
match(pᵢ, v) = σ
─────────────────────────── (E-Match)
match v with ... | pᵢ => tᵢ | ... → σ(tᵢ)


         t → t'
────────────────────────── (E-MatchStep)
match t with ... → match t' with ...
```

Where `match(p, v) = σ` is the pattern matching judgment that produces a substitution σ.

## Pattern Matching Semantics

Pattern matching is defined by the judgment `match(p, v) = σ`, which attempts to match pattern `p` against value `v`, producing a substitution `σ`:

```
match(x, v) = [x ↦ v]
match(_, v) = []
match((), ()) = []
match(true, true) = []
match(false, false) = []
match(0, 0) = []
match(succ p, succ v) = match(p, v)
match((p₁, p₂), (v₁, v₂)) = match(p₁, v₁) ∪ match(p₂, v₂)
match(inl p, inl v) = match(p, v)
match(inr p, inr v) = match(p, v)
match(<l=p>, <l=v>) = match(p, v)
match([], []) = []
match(p::ps, v::vs) = match(p, v) ∪ match(ps, vs)
match(p, v) = fail     (otherwise)
```

## Examples

### Option Type

The option type encodes nullable values:

```
Option τ = Unit + τ

none : Option τ
none = inl[τ] ()

some : τ → Option τ
some = λx:τ. inr[Unit] x

-- Pattern matching on option
getOrDefault : τ → Option τ → τ
getOrDefault = λdefault:τ. λopt:Option τ.
  case opt of
    inl u => default
  | inr x => x
```

### Either Type

The either type represents a choice between two types:

```
Either τ₁ τ₂ = τ₁ + τ₂

left : τ₁ → Either τ₁ τ₂
left = λx:τ₁. inl[τ₂] x

right : τ₂ → Either τ₁ τ₂
right = λx:τ₂. inr[τ₁] x
```

### Lists

```
-- List of natural numbers
myList : List Nat
myList = 0 :: 1 :: 2 :: []

-- Length function (using recursion - not available in STLC!)
-- This requires adding recursion to the language
```

### Records as Named Products

```
Point = {x:Nat, y:Nat}

origin : Point
origin = {x=0, y=0}

getX : Point → Nat
getX = λp:Point. p.x

translate : Point → Nat → Nat → Point
translate = λp:Point. λdx:Nat. λdy:Nat.
  {x=p.x, y=p.y}  -- Note: we can't actually add here without extending Nat ops
```

### Variants as Named Sums

```
Shape = <circle:Nat, square:Nat, rectangle:{width:Nat, height:Nat}>

makeCircle : Nat → Shape
makeCircle = λr:Nat. <circle=r> as Shape

area : Shape → Nat
area = λs:Shape.
  case s of
    <circle=r> => r  -- Simplified: actual area would need multiplication
  | <square=side> => side
  | <rectangle=dims> => dims.width  -- Simplified
```

## Metatheory

### Progress and Preservation

**Theorem (Progress)**: If `⊢ t : τ`, then either `t` is a value or there exists `t'` such that `t → t'`.

**Theorem (Preservation)**: If `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`.

**Proof sketch**: Both proofs extend the proofs from Chapter 2 by induction on the new typing and evaluation rules. The key insight is that each new construct follows the same pattern:
- Products preserve types through both formation and elimination
- Sums require case analysis to eliminate, which type-checks both branches
- Records and variants are just generalized products and sums
- Lists are inductively defined types that preserve element types

### Strong Normalization

**Theorem (Strong Normalization)**: All well-typed terms in STLC + ADTs terminate.

**Proof sketch**: Extends the proof for STLC. The key is showing that:
- Products, records, lists only combine finite, normalizing terms
- Sums, variants require case analysis that leads to normalizing sub-terms
- Pattern matching is just elaborated case analysis

STLC + ADTs remains **not Turing-complete**—we still cannot express general recursion.

### Decidability

**Theorem (Decidable Type Checking)**: Type checking for STLC + ADTs is decidable.

The type checking algorithm is syntax-directed and always terminates.

## Limitations

Despite the increased expressiveness, we still cannot:
1. **Define recursive functions** (no fixed-point operator)
2. **Define recursive types** (no μ operator)
3. **Define parametrically polymorphic functions** (no polymorphism)

These limitations are addressed in subsequent chapters:
- Chapter 4: Adds type inference
- Chapter 5: Adds polymorphism (System F)
- Later chapters: Add recursive types and dependent types

## Implementation

### Project Structure

```
chapter-03-stlc-adt/
├── src/
│   ├── Syntax.hs       -- AST with ADTs and patterns
│   ├── TypeCheck.hs    -- Type checker with pattern type checking
│   ├── Eval.hs         -- CBV evaluation with pattern matching
│   ├── Parser.hs       -- Parser for all constructs
│   └── Pretty.hs       -- Pretty printer
├── test/
│   └── Spec.hs         -- Comprehensive test suite
└── README.md           -- This file
```

### Building and Testing

```bash
stack init
stack build
stack test
```

## Real-World Connections

Algebraic Data Types (ADTs) are everywhere in modern programming. Understanding ADTs from Chapter 3 helps you recognize and effectively use patterns in Rust, TypeScript, Haskell, Swift, Kotlin, and many other languages.

### Where You've Seen This

#### **Rust (Enums = Sum Types + Product Types)**
```rust
// Sum types (enums/variants)
enum Option<T> {
    None,              // Unit variant
    Some(T)            // Product: carries a value
}

// Pattern matching is native
match user_id {
    Some(id) => println!("User: {}", id),
    None => println!("Not logged in")
}

// Result type (Either in Haskell)
enum Result<T, E> {
    Ok(T),
    Err(E)
}
```

#### **TypeScript (Union Types + Discriminated Unions)**
```typescript
// Sum types via union types
type Option<T> = { kind: 'none' } | { kind: 'some'; value: T };

// Product types (tuples and records)
type Pair<A, B> = [A, B];
type User = { name: string; email: string; age: number };

// Pattern matching via discriminated unions
function unwrap<T>(opt: Option<T>): T | null {
    switch (opt.kind) {
        case 'none': return null;
        case 'some': return opt.value;
    }
}
```

#### **Haskell / OCaml / F# (Native ADTs)**
```haskell
-- Sum types (data)
data Maybe a = Nothing | Just a
data Either a b = Left a | Right b

-- Product types (tuples and records)
type Pair a b = (a, b)
data User = User { name :: String, email :: String }

-- Pattern matching
case maybeValue of
    Nothing -> "not found"
    Just x -> "found: " ++ show x
```

#### **Swift (Enums with Associated Values)**
```swift
// Swift enums are true sum types
enum Option<T> {
    case none
    case some(T)
}

// Pattern matching with switch
switch result {
case .success(let value):
    print("Success: \(value)")
case .failure(let error):
    print("Error: \(error)")
}
```

### Problems ADTs Solve

| Problem | Without ADTs | With ADTs |
|---------|--------------|-----------|
| **Null safety** | `null` can appear anywhere → NPE | `Option<T>` makes absence explicit |
| **Error handling** | Exceptions, error codes | `Result<T, E>` type-safe errors |
| **State machines** | Booleans, magic numbers | Variants represent states |
| **Heterogeneous collections** | `Object[]`, type casts | Sum types with type safety |

### Key Concept Mappings

| Chapter 3 Concept | Real-World Feature |
|-------------------|-------------------|
| **Product types** `τ₁ × τ₂` | Tuples, structs, classes |
| **Sum types** `τ₁ + τ₂` | Enums, unions, Either |
| **Records** `{x: τ₁, y: τ₂}` | Objects, structs with named fields |
| **Variants** `<left: τ₁, right: τ₂>` | Tagged unions, discriminated unions |
| **Lists** | Arrays, vectors, linked lists |
| **Pattern matching** | `switch`, `match`, destructuring |

### Why ADTs Matter

1. **Type Safety**: Compiler catches missing cases
2. **Documentation**: Types describe data structure precisely
3. **Refactoring**: Change data type → compiler finds all affected code
4. **No Null**: Option/Maybe replaces null
5. **No Exceptions**: Result/Either for type-safe errors

## References

### Essential Reading

1. **Pierce, Benjamin C.** (2002). *Types and Programming Languages*. MIT Press.
   - Chapter 11: Simple Extensions (Products, Sums, Records, Variants)
   - Chapter 13: References
   - The canonical reference for ADTs in typed lambda calculi

2. **Harper, Robert** (2016). *Practical Foundations for Programming Languages* (2nd ed.).
   - Chapter 11: Product Types
   - Chapter 12: Sum Types
   - Chapter 14: Generic Programming (patterns)

3. **Cardelli, Luca** (1984). "A Semantics of Multiple Inheritance." *Semantics of Data Types*.
   - Early work on record types and subtyping

### Algebraic Data Types Theory

4. **Burstall, Rod M. and Goguen, Joseph A.** (1977). "Putting Theories Together to Make Specifications." *IJCAI*.
   - Foundational work on algebraic specifications

5. **Liskov, Barbara and Zilles, Stephen** (1974). "Programming with Abstract Data Types." *SIGPLAN*.
   - Abstract data types and their importance

### Pattern Matching

6. **Augustsson, Lennart** (1985). "Compiling Pattern Matching." *FPCA*.
   - Classic paper on implementing pattern matching

7. **Wadler, Philip** (1987). "Views: A Way for Pattern Matching to Cohabit with Data Abstraction." *POPL*.
   - Extending pattern matching

8. **Maranget, Luc** (2008). "Compiling Pattern Matching to Good Decision Trees." *ML Workshop*.
   - Efficient compilation of pattern matching

### Records and Variants

9. **Wand, Mitchell** (1987). "Complete Type Inference for Simple Objects." *LICS*.
   - Type inference for records

10. **Rémy, Didier** (1989). "Type Checking Records and Variants in a Natural Extension of ML." *POPL*.
    - Extensible records and variants

## Exercises

1. Add tuple types (n-ary products) as syntactic sugar
2. Implement let-patterns: `let (x, y) = pair in body`
3. Add recursive types using the `μ` operator
4. Implement exhaustiveness checking for pattern matching
5. Add polymorphic lists and implement map/fold
6. Implement records with subtyping (width and depth)
7. Add first-class labels for records/variants
8. Implement extensible records and variants

## Next Chapter

In [Chapter 4](../chapter-04-hindley-milner), we add **type inference** using the Hindley-Milner algorithm, allowing us to write programs without type annotations while maintaining type safety.
