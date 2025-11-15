# Chapter 6: System F-omega - Exercises

These exercises explore higher-kinded types and type operators in System F-omega.

## Exercise 1: Basic Type Operators

Implement basic type-level operators to understand how types form their own lambda calculus.

### 1a. Identity Type Operator

Implement the identity type operator:
```
IdOp = λA::*. A
```

- **Kind**: `* → *`
- **Meaning**: Takes a type and returns that same type
- **Example**: `IdOp Bool` normalizes to `Bool`

**Hint**: Use `TyLam` with kind `KStar` for the parameter.

### 1b. Const Type Operator

Implement the constant type operator that ignores its second argument:
```
ConstOp = λA::*. λB::*. A
```

- **Kind**: `* → * → *`
- **Meaning**: Takes two types and returns the first
- **Example**: `ConstOp Bool Nat` normalizes to `Bool`

**Hint**: Nest two `TyLam` constructors.

### 1c. Compose Type Operators

Implement type operator composition:
```
ComposeOp = λF::* → *. λG::* → *. λA::*. F (G A)
```

- **Kind**: `(* → *) → (* → *) → * → *`
- **Meaning**: Composes two type constructors
- **Example**: `ComposeOp Maybe List Bool` normalizes to `Maybe (List Bool)`

**Learning Objective**: Understand higher-kinded types - types that take types as parameters.

## Exercise 2: List Type Constructor

Implement the Church-encoded List type constructor and its operations.

### 2a. List Type Constructor

Define List using Church encoding at the type level:
```
List = λA::*. ∀R::*. R → (A → R → R) → R
```

- **Kind**: `* → *`
- **Meaning**: A list of A's is a fold - given a nil value and cons function, produce R

### 2b. List Bool

Form the type `List Bool` by applying the List type constructor to Bool.

**Hint**: Use `TyApp listType TyBool`

### 2c. Nil Constructor

Implement the empty list constructor:
```
nil : ∀A::*. List A
nil = ΛA::*. ΛR::*. λnil:R. λcons:A → R → R. nil
```

### 2d. Cons Constructor

Implement the list cons (prepend) constructor:
```
cons : ∀A::*. A → List A → List A
```

**Hint**: Use the fold representation - cons prepends an element.

**Learning Objective**: Understand how algebraic data types can be encoded using higher-kinded types.

## Exercise 3: Maybe Type Constructor

Implement the Maybe (Option) type constructor.

### 3a. Maybe Type Constructor

Define Maybe using Church encoding:
```
Maybe = λA::*. ∀R::*. R → (A → R) → R
```

- **Kind**: `* → *`
- **Meaning**: Optional value - either nothing or just a value

### 3b. Nothing Constructor

Implement the Nothing case:
```
nothing : ∀A::*. Maybe A
```

### 3c. Just Constructor

Implement the Just case:
```
just : ∀A::*. A → Maybe A
```

**Learning Objective**: See how Option types emerge from System F-omega encodings.

## Exercise 4: Either Type Constructor

Implement the Either (sum) type constructor.

### 4a. Either Type Constructor

Define Either:
```
Either = λA::*. λB::*. ∀R::*. (A → R) → (B → R) → R
```

- **Kind**: `* → * → *`
- **Meaning**: Disjoint union - either a value of type A or type B

### 4b. Either Bool Nat

Form the type `Either Bool Nat`.

### 4c. Left Injection

Implement the left constructor:
```
left : ∀A::*. ∀B::*. A → Either A B
```

### 4d. Right Injection

Implement the right constructor:
```
right : ∀A::*. ∀B::*. B → Either A B
```

**Learning Objective**: Understand how sum types work at the type level.

## Exercise 5: Functor Type Class (Conceptual)

### 5a. Functor Kind

While we can't fully encode type classes in System F-omega, we can understand their kinds.

A Functor takes a type constructor and produces constraints/evidence:
```
Functor :: (* → *) → *
```

**Discussion**: What does it mean for a kind to be `(* → *) → *`? This takes a type constructor (like List or Maybe) and produces a type (the functor instance).

**Learning Objective**: Understand how type classes relate to higher-kinded types.

## Exercise 6: Type-Level Church Encodings

### 6a. Type-Level Church Booleans

Church booleans can exist at both term and type level:
```
CBool = ∀A::*. A → A → A
```

Define this type.

### 6b. Type-Level If

Implement type-level conditional:
```
TyIf = λC::*. λT::*. λF::*. C T F
```

- **Kind**: `* → * → * → *`
- **Meaning**: If C is a Church boolean type, apply it to T and F

**Learning Objective**: See how type-level computation works.

## Exercise 7: Product and Sum at Type Level

### 7a. Product Type Operator

Define the product type using Church encoding:
```
Product = λA::*. λB::*. ∀R::*. (A → B → R) → R
```

- **Kind**: `* → * → *`

### 7b. Sum Type Operator

Define the sum type (note: this is the same as Either):
```
Sum = λA::*. λB::*. ∀R::*. (A → R) → (B → R) → R
```

- **Kind**: `* → * → *`

**Learning Objective**: Understand how basic type constructors emerge from System F-omega.

## Exercise 8: Advanced Type Operators (Optional Challenges)

### 8a. Flip Type Operator

Implement a type operator that flips the order of arguments:
```
Flip = λF::* → * → *. λA::*. λB::*. F B A
```

- **Kind**: `(* → * → *) → * → * → *`

### 8b. Twice Operator

Implement a type operator that applies a type constructor twice:
```
Twice = λF::* → *. λA::*. F (F A)
```

- **Kind**: `(* → *) → * → *`
- **Example**: `Twice Maybe Bool` = `Maybe (Maybe Bool)`

### 8c. Fix Point Operator (Challenging)

Can you define a fixed-point operator at the type level? What would its kind be?

## Theoretical Exercises

### T1. Normalization

**Question**: Does type-level beta reduction in System F-omega always terminate?

**Answer**: Yes! System F-omega has the strong normalization property - all type-level reductions terminate. This is because the kind system prevents self-application.

### T2. Kind Inference

**Question**: Given a type expression, can we always infer its kind?

**Answer**: Yes, kind inference in System F-omega is decidable and can be done using a kinding algorithm similar to type inference.

### T3. Expressiveness

**Question**: Can we encode System F in System F-omega?

**Answer**: Yes! System F is a subset of System F-omega. Every System F type has kind `*` in System F-omega.

## References

1. **Girard** (1972) - "Interprétation fonctionnelle et élimination des coupures"
   - Original presentation of System F-omega

2. **Pierce** (2002) - *Types and Programming Languages*
   - Chapter 30: Higher-Order Polymorphism
   - Excellent explanation with examples

3. **Barendregt** (1992) - "Lambda Calculi with Types"
   - Comprehensive treatment in *Handbook of Logic in Computer Science*

4. **Jones, Peyton Jones, Meijer** (1997) - "Type Classes: An Exploration of the Design Space"
   - Shows how Haskell's type classes relate to System F-omega

## Next Steps

After completing these exercises, you'll understand:
- How types can parameterize over other types
- The kind system that prevents ill-formed types
- How common type constructors (List, Maybe, Either) emerge naturally
- The connection between System F-omega and real programming languages like Haskell

In Chapter 7, we'll begin exploring dependent types where types can depend on *values*, not just other types!
