# Checkpoint 4: Dependent Types (After Chapters 7-8)

## Coverage
Full dependent type theory with universes and equality.

## Time: 90-120 minutes

---

## Critical Concepts

1. **Pi vs Sigma types**: When do you use each?

2. **Universe hierarchy**: Why do we need Type : Type1 : Type2 : ...?

3. **Definitional vs propositional equality**: Explain the difference.

4. **J eliminator**: What is it for?

5. **Inductive families**: How is Vec different from List?

---

## Proof Problems

6. **Prove in dependent types**:
   - Symmetry: `∀A. ∀x y. x = y → y = x`
   - Transitivity: `∀A. ∀x y z. x = y → y = z → x = z`

7. **Vector operations**:
   - Implement: `vappend : Π(m n:Nat). Vec A m → Vec A n → Vec A (m+n)`
   - Type of: `vhead : Π(n:Nat). Vec A (succ n) → A`

8. **Curry-Howard**:
   - What proposition does `Π(A:Type). A → A` represent?
   - What proposition does `Π(A:Type). Π(B:Type). A → B → A` represent?
   - What proposition does `Empty → Π(A:Type). A` represent?

---

## Integration Question

9. **Journey**: Trace the evolution of the identity function:
   - Ch1: `\x. x`
   - Ch2: `\x:T. x`
   - Ch4: `\x. x` (inferred as ∀a. a → a)
   - Ch5: `/\A. \x:A. x`
   - Ch7: `\(A:Type). \(x:A). x`
   - Ch8: Same but with universes

   What changed at each step? Why?

---

## Self-Assessment

**Concepts (/5)**: Can you explain Π, Σ, universes, equality?
**Implementation (/5)**: Can you write dependently-typed functions?
**Proving (/5)**: Can you construct equality proofs?

**Total /15**:
- **13-15**: 🎓 Mastery! You understand dependent types!
- **10-12**: ✅ Solid understanding, minor gaps
- **< 10**: ⚠️ Review Ch7-8

---

## Congratulations!

If you've completed all 4 checkpoints, you've mastered the journey from lambda calculus to full dependent types - a foundation for all of type theory!

**Next steps**:
- Real proof assistants (Agda, Coq, Lean)
- Verified programming projects
- Original research in type theory
- Advanced topics (HoTT, cubical type theory, etc.)

**You've reached the summit!** 🏔️

[Full solutions available in separate document]
