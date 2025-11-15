# Type Systems Glossary

A comprehensive reference for terminology used throughout the course.

## A

**Abstract Syntax Tree (AST)**
A tree representation of the syntactic structure of a program. In our implementations, this is represented by data types like `Term` and `Type`.

**ADT (Algebraic Data Type)**
A composite type formed by combining other types. Includes:
- **Product types**: Pairs, tuples, records (both components)
- **Sum types**: Tagged unions, variants (one of several components)

**Alpha Conversion (α-conversion)**
Renaming bound variables in a term without changing its meaning.
Example: `λx. x ≡ λy. y`

**Alpha Equivalence**
Two terms are alpha-equivalent if they are identical up to renaming of bound variables.

**Arity**
The number of arguments a function or constructor takes.

## B

**Beta Reduction (β-reduction)**
The fundamental computation step in lambda calculus: applying a function to an argument.
`(λx. t) v → t[x := v]`

**Bidirectional Type Checking**
A type checking algorithm that alternates between:
- **Checking mode**: Verify a term has a given type
- **Synthesis mode**: Infer the type of a term

Used in System F and dependent type theories.

**Bound Variable**
A variable that appears within the scope of a λ-abstraction binding it.
In `λx. x y`, `x` is bound, `y` is free.

## C

**Call-by-Name (CBN)**
Evaluation strategy where arguments are substituted unevaluated.
`(λx. t) s → t[x := s]` (even if `s` is not a value)

**Call-by-Value (CBV)**
Evaluation strategy where arguments are evaluated before substitution.
`(λx. t) v → t[x := v]` (only when `v` is a value)

**Church Encoding**
Representation of data and operations using only lambda abstractions.
- Booleans: `true = λt. λf. t`, `false = λt. λf. f`
- Numerals: `0 = λf. λx. x`, `1 = λf. λx. f x`, `2 = λf. λx. f (f x)`

**Church-Rosser Property**
See: Confluence

**Closed Term**
A term with no free variables. Also called a **combinator**.

**Confluence**
If `t → t₁` and `t → t₂`, then there exists `t'` such that `t₁ →* t'` and `t₂ →* t'`.
Ensures evaluation order doesn't matter for the final result.

**Constructor**
A function that builds values of an inductive type.
Example: `Cons : A → List A → List A`

**Context (Type Context)**
A mapping from variables to types, written Γ (gamma).
Represents assumptions about variable types.

**Curry-Howard Correspondence**
Deep connection between:
- **Logic**: Propositions, proofs
- **Type Theory**: Types, terms

| Logic | Types |
|-------|-------|
| Proposition | Type |
| Proof | Term |
| Implication (A → B) | Function type |
| Conjunction (A ∧ B) | Product type |
| Disjunction (A ∨ B) | Sum type |
| True | Unit type |
| False | Empty type |

## D

**Decidability**
A property or problem is decidable if there exists an algorithm that always terminates with yes/no.
- Type checking in STLC: **Decidable**
- Type inference in System F: **Undecidable**

**Definitional Equality**
Two terms are definitionally equal if they reduce to the same normal form.
Written: `t₁ ≡ t₂`

**Dependent Function (Π-type)**
A function type where the result type can depend on the argument value.
`Π(x:A). B` where `B` may contain `x`.

**Dependent Pair (Σ-type)**
A pair type where the second component's type depends on the first component's value.
`Σ(x:A). B` where `B` may contain `x`.

**Dependent Type**
A type that depends on a value.
Example: `Vec n A` (vectors of length `n`)

## E

**Eliminator**
A function that performs structural recursion on an inductive type.
Example: `natElim` for natural numbers, `boolElim` for booleans.

**Erasure**
Removing type annotations from terms to get untyped lambda calculus.

**Eta Reduction (η-reduction)**
`λx. f x → f` (when `x` is not free in `f`)

**Eta Expansion (η-expansion)**
`f → λx. f x`

**Existential Type**
A type that hides implementation details.
`∃α. τ` - "there exists a type α such that τ"

## F

**Free Variable**
A variable not bound by any enclosing λ-abstraction.
In `λx. x y`, `y` is free.

**Fresh Variable**
A variable name not already used in the current context.
Essential for avoiding name capture during substitution.

## G

**Generalization**
Converting a monotype to a polytype by adding universal quantifiers.
In Hindley-Milner: `τ ⟿ ∀α. τ` (for free type variables α)

**Girard's Paradox**
A type-theoretic paradox arising from `Type : Type`.
Analogous to Russell's paradox. Prevented by universe hierarchies.

## H

**Higher-Kinded Type**
A type constructor that takes type constructors as arguments.
Example: `Functor : (* → *) → *`

**Hindley-Milner (HM)**
Type inference algorithm featuring:
- Complete type inference (no annotations needed)
- Let-polymorphism
- Principal types

Used in ML, Haskell, OCaml.

## I

**Impredicative**
A type system where quantification can include the type being defined.
Example: In System F, `∀α. α → α : *` even though it quantifies over `*`.

**Inductive Family**
An inductive type indexed by one or more values.
Example: `Vec : Nat → Type → Type`

**Inductive Type**
A type defined by its constructors.
Example: `data Nat = Zero | Succ Nat`

**Inference**
Automatically determining types without explicit annotations.

**Instantiation**
Converting a polytype to a monotype by substituting type variables.
`∀α. α → α ⟿ Int → Int`

**Intensional Equality**
Equality based on syntactic structure (after normalization).
Stricter than extensional equality.

## J

**J Eliminator**
The elimination principle for propositional equality.
States: to prove a property for all equalities, it suffices to prove it for reflexivity.

**Judgment**
A formal assertion about terms, types, or contexts.
Examples:
- `Γ ⊢ t : τ` (typing judgment)
- `t → t'` (reduction judgment)

## K

**K Axiom**
States that all proofs of `x = x` are equal to `refl x`.
Controversial; rejected in Homotopy Type Theory.

**Kind**
The "type of a type".
- `*` (star): Kind of proper types like `Nat`, `Bool`
- `* → *`: Kind of type constructors like `List`, `Maybe`
- `* → * → *`: Kind of binary type constructors

**Kinding Judgment**
`τ :: κ` - "type τ has kind κ"

## L

**Lambda Abstraction**
Function definition in lambda calculus: `λx. t`

**Lambda Calculus**
A formal system for expressing computation using only:
- Variables: `x`
- Abstraction: `λx. t`
- Application: `t₁ t₂`

**Let-Polymorphism**
In Hindley-Milner, variables bound by `let` are polymorphic.
`let id = λx. x in ...` - `id` has type `∀α. α → α`

**Leibniz Equality**
Alternative formulation of equality:
`x = y ≡ ∀P. P x → P y`
"Equal things satisfy the same predicates"

## M

**Metavariable**
A variable standing for an unknown type in type inference.
Also called: type variable, unification variable.

**Monotype**
A type with no universal quantifiers (∀).
Example: `Int → Bool`

**Most General Unifier (MGU)**
The substitution that unifies two types with minimal instantiation.

## N

**η-reduction/expansion**: See Eta Reduction/Expansion

**Normal Form**
A term that cannot be reduced further.

**Normal Order Reduction**
Evaluation strategy that always reduces the leftmost-outermost redex first.
Guaranteed to find normal form if it exists.

**Normalization**
The process of reducing a term to normal form.

## O

**Occurs Check**
In unification, checking that a type variable doesn't occur in the type it's being unified with.
Prevents infinite types like `α = α → α`.

## P

**Parametricity**
Property of polymorphic functions: behavior is uniform across all types.
Enables "theorems for free" - properties derivable from types alone.

**Pattern Matching**
Decomposing data by matching against constructors.
```haskell
match xs with
  | Nil -> ...
  | Cons x xs' -> ...
```

**Pi Type (Π-type)**
See: Dependent Function

**Polytype**
A type with universal quantifiers.
Example: `∀α. α → α`

**Predicative**
A type system where quantification cannot include the type being defined.
Example: Our dependent types have predicative universes.

**Preservation**
Type safety property: If `Γ ⊢ t : τ` and `t → t'`, then `Γ ⊢ t' : τ`.
Also called: **Subject Reduction**.

**Principal Type**
The most general type that can be assigned to a term.
Hindley-Milner guarantees principal types exist.

**Product Type**
A type containing multiple values.
`A × B`, `(A, B)`, or record types.

**Progress**
Type safety property: If `⊢ t : τ` then either `t` is a value or `t → t'`.
Well-typed terms don't get stuck.

**Propositional Equality**
Equality as a type that can be inhabited by proof terms.
`Eq A x y` - the type of proofs that `x = y` in type `A`.

## Q

**Quantification**
Binding type variables:
- **Universal (∀)**: For all types
- **Existential (∃)**: There exists a type

## R

**Redex**
A **red**ucible **ex**pression.
Example: `(λx. t) v` is a β-redex.

**Reduction**
Transforming a term by applying reduction rules.

**Reflexivity**
Property of equality: `∀x. x = x`
Represented by the `refl` constructor.

**Refinement Type**
A type with a logical predicate.
Example: `{x:Int | x > 0}` (positive integers)

## S

**Sigma Type (Σ-type)**
See: Dependent Pair

**Simply Typed Lambda Calculus (STLC)**
Lambda calculus with simple types (no polymorphism).
Types: base types, function types.

**Strong Normalization**
Every reduction sequence terminates in a normal form.
STLC, System F, and our dependent types are strongly normalizing.

**Structural Induction**
Proof technique: prove property for all cases of a data structure.

**Structural Recursion**
Recursion that processes sub-structures of the input.
Guaranteed to terminate.

**Subject Reduction**
See: Preservation

**Substitution**
Replacing a variable with a term: `t[x := s]`

**Sum Type**
A type representing a choice between alternatives.
`A + B`, `Either A B`, or variant types.

**Symmetry**
Property of equality: `x = y → y = x`

**System F**
Lambda calculus with parametric polymorphism.
Also called: **second-order lambda calculus**, **polymorphic lambda calculus**.

**System F-omega (Fω)**
Extension of System F with higher-kinded types and type operators.

## T

**Transitivity**
Property of equality: `x = y → y = z → x = z`

**Type**
A classification of terms.
Restricts what operations can be performed.

**Type Abstraction**
Introducing a type variable: `Λα. t` (System F)

**Type Application**
Applying a type to a polymorphic term: `t [τ]` (System F)

**Type Checker**
Algorithm verifying `Γ ⊢ t : τ` for given Γ, t, τ.

**Type Constructor**
A function from types to types.
Example: `List : * → *`

**Type Erasure**
See: Erasure

**Type Family**
A function from values to types.
Example: `Vec : Nat → Type → Type`

**Type Inference**
Algorithm computing τ given Γ and t.

**Type Operator**
See: Type Constructor

**Type Safety**
Well-typed programs don't go wrong.
Formalized as Progress + Preservation.

**Type Scheme**
See: Polytype

**Type Variable**
A variable ranging over types, usually written α, β, γ.

## U

**Unification**
Finding a substitution making two types equal.
Central to Hindley-Milner type inference.

**Universe**
A type of types.
In our system: `Type 0`, `Type 1`, `Type 2`, ...

**Universe Hierarchy**
Stratification of universes to avoid paradoxes:
`Type 0 : Type 1 : Type 2 : ...`

**Universe Polymorphism**
Quantification over universe levels.
Example: `∀(i:Level). Π(A:Type i). A → A`

## V

**Value**
A term in normal form that represents a result.
Examples: `λx. t`, `Zero`, `True`, `(v₁, v₂)`

**Variable**
A name representing an unknown or parameter.

## W

**Weak Head Normal Form (WHNF)**
A term reduced just enough to determine its outermost constructor.
Used in lazy evaluation.

**Well-Founded Recursion**
Recursion with a decreasing measure guaranteeing termination.

**Well-Typed**
A term for which type checking succeeds: `Γ ⊢ t : τ`

## Cross-References

### By Chapter

- **Chapter 1**: Lambda calculus, Beta reduction, Church encoding, Normal form, Substitution
- **Chapter 2**: STLC, Type safety, Progress, Preservation, Product/Sum types
- **Chapter 3**: ADT, Pattern matching, Exhaustiveness
- **Chapter 4**: Hindley-Milner, Unification, Let-polymorphism, Principal type
- **Chapter 5**: System F, Parametricity, Type abstraction/application
- **Chapter 6**: System F-omega, Kind, Higher-kinded type, Type operator
- **Chapter 7**: Dependent type, Pi type, Sigma type, Type-in-Type
- **Chapter 8**: Universe hierarchy, Propositional equality, J eliminator, Inductive family

### Related Concepts

- **Type checking** ↔ Type inference ↔ Bidirectional checking
- **Progress** ↔ Preservation ↔ Type safety
- **Alpha equivalence** ↔ Beta reduction ↔ Eta conversion
- **Generalization** ↔ Instantiation ↔ Let-polymorphism
- **Unification** ↔ Substitution ↔ Most general unifier

## Further Reading

For detailed explanations, see:
- Individual chapter READMEs for context-specific definitions
- Papers referenced in each chapter for formal treatments
- Pierce's "Types and Programming Languages" (TAPL) for comprehensive coverage
