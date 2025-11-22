# Checkpoint 3: Polymorphism (After Chapters 5-6)

## Coverage
System F explicit polymorphism and System F-omega higher-kinded types.

## Time: 60-75 minutes

---

## Key Concepts to Verify

1. **Type abstraction vs type application**: Explain `/\A. t` and `t [T]`

2. **Parametricity**: Why can't `∀A. A → A` inspect its argument?

3. **Church encodings**: How do we represent data using only functions?

4. **Kinds**: Explain `*`, `* → *`, and `(* → *) → *`

5. **Higher-kinded types**: What does `Functor` abstract over?

---

## Practical Problems

6. **Implement in System F**:
   - Church booleans (Bool, true, false, if)
   - Church pairs (Pair, pair, fst, snd)

7. **Type these in System F-omega**:
   - `/\F::*->*. /\A::*. /\B::*. (A->B) -> F A -> F B`
   - `List Nat` where `List :: * → *`

8. **Compare**:
   - System F: `∀A. A → A`
   - HM: Inferred polymorphism
   - Dependent: `Π(A:Type). A → A`
   What's the same? What's different?

---

## Self-Assessment

**Understanding (/5)**:
- Can you implement Church encodings?
- Can you explain parametricity?
- Can you work with kinds?

**Score 12-15/15**: Ready for dependent types!
**Score < 12**: Review Ch5-6

---

[Full answer key available after attempt]
