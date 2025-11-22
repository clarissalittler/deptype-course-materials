# Checkpoint 2: Structured Data & Inference (After Chapters 3-4)

## Purpose
Verify understanding of ADTs and type inference before advanced polymorphism.

## Time Estimate
75-90 minutes

---

## Part A: ADTs (30 minutes)

### Concept Questions

1. **Explain product vs sum types**. Give a real-world example of when you'd use each.

2. **Why do sum types require type annotations** in our system?
   ```
   inl true : ???    -- What goes here and why?
   ```

3. **Pattern matching**: What's wrong with this?
   ```
   case x of
     inl a => a + 1
   ```

### Practical Problems

4. **Implement using ADTs**:
   ```
   a) Option type: map_option : (A -> B) -> Option A -> Option B
   b) Result type (error handling): get_or_default : Result A -> A -> A
   ```

5. **Type these expressions**:
   ```
   a) pair (inl true : Bool + Nat) zero
   b) case (pair true zero) of (x,y) => if x then y else succ y
   ```

---

## Part B: Hindley-Milner (35 minutes)

### Concept Questions

6. **Explain let-polymorphism**. Why does this work?
   ```
   let id = \x. x in (id 1, id true)
   ```
   But this doesn't?
   ```
   (\id. (id 1, id true)) (\x. x)
   ```

7. **What is unification**? Give an example of:
   - Successful unification
   - Failed unification (with occurs check)

8. **Principal types**: What makes a type "most general"?

### Practical Problems

9. **Infer types** (write the most general type):
   ```
   a) \x. x
   b) \x. \y. x
   c) \f. \g. \x. f (g x)
   d) \x. (x 1, x true)    -- Can this be typed?
   ```

10. **Algorithm W**: Show unification steps for:
    ```
    \f. \x. f (f x)
    ```

11. **Debug this type error**:
    ```
    let pair_apply = \f. \g. \x. (f x, g x) in
    pair_apply (\y. y + 1) (\z. not z) 5
    ```
    What's wrong? How to fix?

---

## Part C: Integration (20 minutes)

12. **Compare type systems**:

| Feature | STLC (Ch2) | STLC+ADTs (Ch3) | HM (Ch4) |
|---------|-----------|----------------|----------|
| Annotations needed? | ? | ? | ? |
| Polymorphism? | ? | ? | ? |
| Data structures? | ? | ? | ? |

13. **Design question**: Your language needs:
    - Optional values
    - No type annotations
    - Type safety

    Which system (Ch2, Ch3, or Ch4) and why?

14. **True/False**:
    - [ ] HM can infer types for all System F programs
    - [ ] ADTs can be encoded in pure lambda calculus
    - [ ] Let-polymorphism is the same as System F polymorphism
    - [ ] Unification always succeeds if a program is well-typed

---

## Self-Assessment Rubric

**Part A (ADTs)**: ___/5
- 5: Fluent with products, sums, pattern matching
- 3: Can use ADTs but sometimes confused
- 1: Don't understand ADTs

**Part B (HM)**: ___/5
- 5: Understand inference algorithm, can debug type errors
- 3: Know polymorphism basics, struggle with algorithm
- 1: Don't understand type inference

**Part C (Integration)**: ___/5
- 5: Clear understanding of tradeoffs between systems
- 3: See some differences
- 1: Systems seem unrelated

**Total**: ___/15

### Interpretation:

**12-15**: ✅ Ready for System F!
**9-11**: ⚠️  Review weak areas
**< 9**: ❌ Review Ch3-4

---

## Answer Hints

1. **Product**: "AND" (tuple of name AND age)
   **Sum**: "OR" (result is success OR error)

2. Need annotation because both `A + B` and `C + D` could have `inl` - ambiguous!

6. Let-bound variables are generalized (∀a. a → a), lambda-bound are not!

9. Types:
   - a) ∀a. a → a
   - b) ∀a b. a → b → a
   - c) ∀a b c. (b → c) → (a → b) → a → c
   - d) NOT TYPEABLE (λ used monomorphically)

11. **Problem**: f requires Int→?, g requires Bool→?, but x is one type
    **Fix**: Use let for polymorphic f and g, or call twice

13. **Answer**: Chapter 4 (HM) - has both optional values (via ADTs or Church encoding) and no annotations

14. **T/F**: F, T, F, F

---

**This checkpoint ensures you're ready for explicit polymorphism and beyond!**
