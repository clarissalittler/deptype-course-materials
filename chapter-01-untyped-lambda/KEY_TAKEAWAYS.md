# Chapter 1: Key Takeaways

## The Big Picture

**Untyped lambda calculus is the foundation of all functional programming.** Everything in this course builds on these three constructs: variables, abstraction (λ), and application.

---

## Core Concepts

### 1. Three Building Blocks
```
Variables:    x, y, z
Abstraction:  λx. t      (functions)
Application:  t₁ t₂      (function calls)
```

**That's it.** These three constructs can encode any computable function.

### 2. Beta-Reduction is Computation
```
(λx. t) v  →  [x ↦ v]t
```
This single rule is the heart of computation in lambda calculus. Function application = substitution.

### 3. Substitution Must Avoid Capture
**The most common mistake**: Naive substitution can capture free variables.

```
WRONG: [y ↦ x](λx. y) = λx. x  (meaning changed!)
RIGHT: [y ↦ x](λx. y) = λz. x  (α-convert first)
```

### 4. Evaluation Order Matters
- **Call-by-value**: Evaluate arguments first (most languages)
- **Call-by-name**: Substitute unevaluated (lazy)
- **Normal order**: Always finds normal form if one exists

---

## Most Important Rules

### Free Variables
```
FV(x) = {x}
FV(λx. t) = FV(t) \ {x}
FV(t₁ t₂) = FV(t₁) ∪ FV(t₂)
```

### Substitution (Capture-Avoiding)
```
[x ↦ s]x = s
[x ↦ s]y = y                    (if x ≠ y)
[x ↦ s](λx. t) = λx. t          (shadowing)
[x ↦ s](λy. t) = λy. [x ↦ s]t   (if y ∉ FV(s))
[x ↦ s](λy. t) = λz. [x ↦ s][y ↦ z]t  (rename if y ∈ FV(s))
```

---

## What You Should Be Able To Do

After this chapter, you should be able to:

- [ ] Parse lambda terms and identify their structure
- [ ] Compute free variables of any term
- [ ] Perform capture-avoiding substitution
- [ ] Reduce terms using β-reduction
- [ ] Explain why `(λx. x x) (λx. x x)` never terminates
- [ ] Encode booleans, numbers, and pairs as functions
- [ ] Explain the Y combinator's role in recursion

---

## Common Pitfalls

1. **Forgetting capture-avoidance** in substitution
2. **Left vs. right association**: `a b c = (a b) c`, not `a (b c)`
3. **Confusing bound and free** variables
4. **Expecting termination**: Not all terms have normal forms!

---

## Connection to Next Chapter

Chapter 2 adds **types** to prevent errors:
- No more `(λx. x x) (λx. x x)` infinite loops
- Functions must declare their input/output types
- Type checking ensures programs "make sense"

**The trade-off**: We lose some expressiveness (self-application) but gain safety guarantees.

---

## One-Sentence Summary

> Lambda calculus shows that functions alone are enough to compute anything, but without types, we have no guarantees about what our programs will do.
