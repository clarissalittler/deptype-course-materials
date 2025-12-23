# Chapter 19: Bidirectional Type Checking - Lesson Plan

**Estimated Total Time**: 10-14 hours

## Prerequisites

Before starting this chapter, ensure you understand:
- [ ] Simply typed lambda calculus
- [ ] Basic type checking: contexts, judgments, derivations
- [ ] Function types and application
- [ ] Polymorphism basics (forall types)

## Learning Objectives

By the end of this chapter, you will be able to:
1. Distinguish between inference and checking modes
2. Classify constructs as introduction or elimination forms
3. Apply the subsumption rule correctly
4. Implement a bidirectional type checker
5. Decide where annotations are needed
6. Extend bidirectional typing to new constructs

---

## Lesson 1: The Two Modes (2-3 hours)

### Learning Goals
- Understand inference (⇒) vs checking (⇐) modes
- See why we need both
- Learn the core intuition

### Activities

1. **Read** README.md sections: Overview, The Two Judgments

2. **Understand the notation**:
   - `Γ ⊢ e ⇒ A` : "In context Γ, synthesize type A for e"
   - `Γ ⊢ e ⇐ A` : "In context Γ, check e against type A"

3. **The key insight**:
   - **Inference**: We compute the type from the term
   - **Checking**: We verify the term matches a known type

4. **Why two modes?**
   Consider `λx. x`:
   - Can we infer its type? No! Could be `Bool → Bool`, `Nat → Nat`, etc.
   - But can we *check* it has type `Bool → Bool`? Yes!

5. **Experiment** with the REPL:
   ```
   stack exec bidir-repl
   bidir> \x. x           -- Cannot infer
   bidir> \(x : Bool). x  -- Can infer: Bool → Bool
   bidir> :check \x. x : Bool -> Bool  -- Can check!
   ```

### Self-Check Questions
- [ ] When do we use inference mode?
- [ ] When do we use checking mode?
- [ ] Why can't we infer the type of an unannotated lambda?

---

## Lesson 2: Introduction vs Elimination (2-3 hours)

### Learning Goals
- Classify constructs by mode
- Understand the introduction/elimination pattern
- See how modes propagate

### Activities

1. **Read** README.md: When to use each mode (table)

2. **The pattern**:
   - **Introduction forms** (construct values): Check
   - **Elimination forms** (use values): Infer

   | Form | Construct | Mode | Example |
   |------|-----------|------|---------|
   | Intro | Lambda | ⇐ | `λx. e` |
   | Elim | Application | ⇒ | `f x` |
   | Intro | Pair | ⇐ | `(a, b)` |
   | Elim | Projection | ⇒ | `fst p` |
   | Intro | Injection | ⇐ | `inl x` |
   | Elim | Case | ⇒ | `case e of ...` |

3. **Why this pattern?**
   - Intros create ambiguity (which function type? which sum type?)
   - Elims resolve ambiguity (the function tells us what it expects)

4. **Study** `src/TypeCheck.hs`:
   - Find the `infer` function
   - Find the `check` function
   - Note which constructs appear in which

5. **Practice**: Classify these as intro or elim:
   - `fst`, `snd`
   - `inl`, `inr`
   - `case`
   - `Λα. e` (type abstraction)
   - `e [A]` (type application)

### Self-Check Questions
- [ ] What makes a form an introduction?
- [ ] Why do eliminations infer?
- [ ] Where does type information "flow"?

---

## Lesson 3: Core Rules (2-3 hours)

### Learning Goals
- Learn the key typing rules
- Understand mode switching
- See how subsumption works

### Activities

1. **Read** README.md: Core Rules section

2. **Study the inference rules**:
   ```
   Variables: x : A ∈ Γ
              ─────────
              Γ ⊢ x ⇒ A

   Application: Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
                ────────────────────────────────
                Γ ⊢ e₁ e₂ ⇒ B
   ```

3. **Study the checking rules**:
   ```
   Lambda: Γ, x:A ⊢ e ⇐ B
           ─────────────────
           Γ ⊢ (λx. e) ⇐ A → B
   ```

4. **The crucial subsumption rule**:
   ```
   Γ ⊢ e ⇒ A    A = B
   ────────────────────
   Γ ⊢ e ⇐ B
   ```

   "If we can infer type A, and A equals the expected type B, checking succeeds."

5. **Trace through derivations**:
   - `(λ(x:Bool). x) true` ⇒ ?
   - `(λx. x : Bool → Bool) true` ⇒ ?

### Self-Check Questions
- [ ] How does application switch modes?
- [ ] When is subsumption applied?
- [ ] What role do annotations play?

---

## Lesson 4: Implementation (2-3 hours)

### Learning Goals
- Implement the two mutually recursive functions
- Handle mode switching correctly
- Produce good error messages

### Activities

1. **Study** `src/TypeCheck.hs` in detail:
   ```haskell
   infer :: Ctx -> Term -> Either TypeError Type
   check :: Ctx -> Term -> Type -> Either TypeError ()
   ```

2. **The inference cases**:
   ```haskell
   infer ctx (Var x) = lookupVar ctx x
   infer ctx (App e1 e2) = do
     ty <- infer ctx e1
     case ty of
       TyArr a b -> check ctx e2 a >> return b
       _ -> throwError "Expected function type"
   ```

3. **The checking cases**:
   ```haskell
   check ctx (Lam x e) (TyArr a b) =
     check (extend x a ctx) e b
   check ctx e expected = do
     inferred <- infer ctx e
     unless (inferred == expected) $
       throwError (TypeMismatch expected inferred)
   ```

4. **Run the tests**:
   ```bash
   stack test
   ```

5. **Try breaking things**: What error do you get for:
   - `(\x. x) 5`
   - `true false`
   - `:check \x. x : Nat`

### Self-Check Questions
- [ ] Why is `check` the fallback in `check`?
- [ ] How are type errors reported?
- [ ] What happens if you forget a case?

---

## Lesson 5: Annotations and Polymorphism (2-3 hours)

### Learning Goals
- Know when annotations are needed
- Understand type abstraction and application
- See higher-rank patterns

### Activities

1. **The annotation trick**:
   When you can't infer, add an annotation:
   ```
   \x. x              -- Cannot infer
   (\x. x : A -> A)   -- Now has type A -> A
   ```

2. **Type abstraction** (checked):
   ```
   Γ ⊢ e ⇐ A
   ─────────────────
   Γ ⊢ (Λα. e) ⇐ ∀α.A
   ```

3. **Type application** (inferred):
   ```
   Γ ⊢ e ⇒ ∀α.A
   ─────────────────────
   Γ ⊢ e [B] ⇒ A[α := B]
   ```

4. **Practice with polymorphism**:
   ```
   bidir> :check (\\x. x) : forall a. a -> a
   bidir> (\\x. x : forall a. a -> a) [Bool]
   bidir> (\\x. x : forall a. a -> a) [Bool] true
   ```

5. **Higher-rank example**:
   ```
   f : (forall a. a -> a) -> Nat
   f id = id 42
   ```

### Self-Check Questions
- [ ] Where do annotations propagate from?
- [ ] Why is Λ checked and [A] inferred?
- [ ] How do you use a polymorphic function?

---

## Lesson 6: Exercises and Extensions (2-3 hours)

### Activities

1. **Complete exercises** from `exercises/EXERCISES.md`:
   - Mode classification
   - Derivation trees
   - Annotation placement
   - Adding new constructs

2. **Extension ideas**:
   - Add subtyping: change `A = B` to `A <: B`
   - Add type holes: `_` that gets reported
   - Add let bindings with polymorphism

3. **Run all tests**:
   ```bash
   stack test
   ```

4. **Self-assessment**: Can you...
   - [ ] Classify any construct by mode?
   - [ ] Write a derivation tree?
   - [ ] Add a new construct to the checker?
   - [ ] Explain when annotations are needed?

---

## Progress Tracker

### Lesson 1: The Two Modes
- [ ] Understood inference vs checking
- [ ] Experimented with REPL
- [ ] See why both are needed

### Lesson 2: Intro vs Elim
- [ ] Can classify constructs
- [ ] Understand mode propagation
- [ ] Studied TypeCheck.hs

### Lesson 3: Core Rules
- [ ] Know inference rules
- [ ] Know checking rules
- [ ] Understand subsumption

### Lesson 4: Implementation
- [ ] Traced through code
- [ ] Ran tests
- [ ] Understand error handling

### Lesson 5: Annotations and Polymorphism
- [ ] Know the annotation trick
- [ ] Understand forall
- [ ] Practiced with REPL

### Lesson 6: Exercises
- [ ] Completed exercises
- [ ] All tests pass
- [ ] Can extend the system

---

## Key Takeaways

After completing this chapter, remember:

1. **Two modes**: Infer (⇒) computes types, check (⇐) verifies them
2. **Introduction → Check**: Lambdas, pairs, injections need context
3. **Elimination → Infer**: Application, projection, case extract info
4. **Subsumption bridges modes**: Inferred = expected → checking succeeds
5. **Annotations provide types**: When inference fails, annotate

## Next Steps

After mastering this chapter:
- **Chapter 20 (Denotational)**: Mathematical perspective
- **Research**: Higher-rank types (Dunfield & Krishnaswami)
- **Advanced**: Dependent types with bidirectional checking
