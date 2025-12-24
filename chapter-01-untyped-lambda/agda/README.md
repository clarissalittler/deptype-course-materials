# Agda Formalization: Untyped Lambda Calculus

This directory contains the Agda formalization of the untyped lambda calculus from Chapter 1.

## Modules

| Module | Description |
|--------|-------------|
| `Syntax.agda` | Term syntax using de Bruijn indices, shifting, and substitution |
| `Evaluation.agda` | Small-step operational semantics, values, multi-step reduction |
| `Properties.agda` | Determinism proof, Ω divergence, uniqueness of values |
| `All.agda` | Convenience module that re-exports everything |

## Building

```bash
# Type-check all modules
agda All.agda

# Type-check individual module
agda Syntax.agda
```

## Key Differences from Haskell Implementation

1. **De Bruijn Indices**: The Agda formalization uses de Bruijn indices instead of named variables. This simplifies substitution and avoids alpha-equivalence issues.

2. **Intrinsic vs Extrinsic**: We use an extrinsic approach where terms are defined separately from their properties.

3. **Proofs**: The Agda version includes machine-checked proofs of properties like determinism.

## What's Proven

- **Determinism**: Call-by-value evaluation is deterministic
- **Ω Diverges**: The term (λx. x x)(λx. x x) never reaches a value
- **Unique Values**: If a term reduces to two values, they are equal

## What's NOT Proven (untyped calculus limitations)

- **Progress**: Untyped terms can get stuck (e.g., `x`, `x y`)
- **Normalization**: Terms like Ω never terminate

## Exercises

1. **Add call-by-name semantics**: Define an alternative reduction relation where arguments are not evaluated before substitution.

2. **Prove Church-Rosser**: Implement parallel reduction and prove the diamond property.

3. **Add named variables**: Extend the syntax with string variables and implement alpha-equivalence.

## References

- *Types and Programming Languages* by Benjamin Pierce, Chapters 5-7
- *Programming Language Foundations in Agda* (PLFA) by Wadler et al.
