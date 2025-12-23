# Chapter 0: Prerequisites and Getting Started

**Welcome to the Type Systems course!** This chapter helps you prepare for the journey from untyped lambda calculus to full dependent types.

## Table of Contents

1. [What is This Course About?](#what-is-this-course-about)
2. [Why Study Type Systems?](#why-study-type-systems)
3. [Prerequisites](#prerequisites)
4. [Setting Up Your Environment](#setting-up-your-environment)
5. [How to Read This Course](#how-to-read-this-course)
6. [Reading Formal Notation](#reading-formal-notation)
7. [Haskell Quick Start](#haskell-quick-start)
8. [Study Strategies](#study-strategies)

## What is This Course About?

This course teaches you to **implement type systems from scratch**. You'll build 22 different type checkers and evaluators, each exploring different aspects of type theory:

```
CORE PROGRESSION (Chapters 1-8):
─────────────────────────────────
Untyped λ-calculus
    ↓ (add types)
Simply Typed λ-calculus
    ↓ (add data structures)
STLC with ADTs
    ↓ (add type inference)
Hindley-Milner
    ↓ (add polymorphism)
System F
    ↓ (add higher-kinded types)
System F-omega
    ↓ (unify terms and types)
Dependent Types
    ↓ (add universe hierarchy)
Full Dependent Types

ADVANCED TYPE FEATURES (Chapters 9-16):
───────────────────────────────────────
Subtyping              ← width/depth subtyping, variance
Linear Types           ← resource tracking, multiplicities
Refinement Types       ← predicate refinements, SMT-style
Effect Systems         ← tracking computational effects
Gradual Typing         ← mixing static and dynamic
Row Types              ← extensible records, polymorphic variants
Recursive Types        ← iso/equi-recursive, μ-types
Homotopy Type Theory   ← univalence, higher inductive types

IMPLEMENTATION TECHNIQUES (Chapters 17-22):
───────────────────────────────────────────
Abstract Machines      ← CEK, SECD, Krivine machines
Normalization by Eval  ← semantic normalization
Bidirectional Typing   ← inference/checking modes
Denotational Semantics ← domain theory, fixed points
Module Systems         ← structures, signatures, functors
Constraint Inference   ← two-phase inference, constraint solving
```

**By the end**, you'll understand the foundations of:
- Programming language design and type system implementation
- Type checking, inference, and constraint solving
- Proof assistants (Coq, Agda, Lean)
- Verified programming and formal methods
- Modern language features (subtyping, linear types, effects)
- Compiler implementation techniques (abstract machines, NbE)
- Module systems and large-scale program organization
- Cutting-edge research (HoTT, refinement types, gradual typing)

### Complete Chapter Overview

| Chapter | Topic | Key Concepts |
|---------|-------|--------------|
| 1 | Untyped Lambda Calculus | Variables, abstraction, application, substitution |
| 2 | Simply Typed Lambda | Base types, function types, type checking |
| 3 | STLC with ADTs | Products, sums, records, pattern matching |
| 4 | Hindley-Milner | Algorithm W, unification, let-polymorphism |
| 5 | System F | Explicit polymorphism, ∀ types, parametricity |
| 6 | System F-omega | Kinds, type operators, higher-kinded types |
| 7 | Dependent Types | Pi types, Sigma types, unified terms/types |
| 8 | Full Dependent Types | Universe hierarchy, equality types, inductive families |
| 9 | Subtyping | Width/depth subtyping, variance, Top/Bot |
| 10 | Linear Types | Multiplicities, usage tracking, resource safety |
| 11 | Refinement Types | Predicate refinements, dependent refinements |
| 12 | Effect Systems | Effect tracking, effect polymorphism, handlers |
| 13 | Gradual Typing | Dynamic type, consistency, casts, blame |
| 14 | Row Types | Extensible records, row polymorphism, variants |
| 15 | Recursive Types | Mu types, fold/unfold, iso-recursive |
| 16 | Homotopy Type Theory | Identity types, univalence, HITs |
| 17 | Abstract Machines | CEK, SECD, Krivine machines |
| 18 | Normalization by Evaluation | Semantic domains, quotation, reflection |
| 19 | Bidirectional Typing | Inference/checking modes, annotations |
| 20 | Denotational Semantics | Domains, CPOs, fixed points |
| 21 | Module Systems | Structures, signatures, functors, sealing |
| 22 | Constraint Inference | Constraint generation, solving, elaboration |

## Why Study Type Systems?

### Real-World Problem: Runtime Errors

Consider this JavaScript code:

```javascript
function process(user) {
  return user.name.toUpperCase();
}

process(null); // TypeError: Cannot read property 'name' of null
```

Or this Python code:

```python
def add(x, y):
    return x + y

add("hello", 5)  # TypeError: can only concatenate str (not "int") to str
```

**Type systems prevent these errors at compile time!**

### What Type Systems Give You

1. **Early Error Detection**
   - Catch bugs before running code
   - No more "undefined is not a function"
   - Prevent type confusion attacks

2. **Documentation**
   - Types serve as machine-checked documentation
   - `getUserById : String -> Maybe User` tells you more than a comment

3. **Refactoring Confidence**
   - Change a type definition, compiler finds all affected code
   - Large-scale refactorings become safe

4. **Performance**
   - Compilers use type information for optimization
   - No runtime type checking needed

5. **Correctness**
   - In dependent types, prove your code correct
   - Express and verify properties: "this list is sorted", "this array access is in bounds"

### Real Languages Use These Systems

**Core Type Systems (Chapters 1-8):**
- **Chapter 1-2 (STLC)**: C, Java, Go, TypeScript (basic mode)
- **Chapter 4 (Hindley-Milner)**: Haskell, OCaml, F#, Rust (inference)
- **Chapter 5 (System F)**: Haskell (under the hood), Java generics
- **Chapter 6 (F-omega)**: Haskell type families, Scala higher-kinded types
- **Chapter 7-8 (Dependent Types)**: Agda, Coq, Idris, Lean

**Advanced Type Features (Chapters 9-16):**
- **Chapter 9 (Subtyping)**: Java, TypeScript, Scala, OOP languages
- **Chapter 10 (Linear Types)**: Rust (ownership), Haskell (linear arrows), Clean
- **Chapter 11 (Refinement Types)**: Liquid Haskell, F*, Dafny, Ada/SPARK
- **Chapter 12 (Effect Systems)**: Koka, Eff, OCaml 5.0 (effects), Frank
- **Chapter 13 (Gradual Typing)**: TypeScript, Python (mypy), Racket, Typed Clojure
- **Chapter 14 (Row Types)**: PureScript, OCaml (objects), Elm (records)
- **Chapter 15 (Recursive Types)**: ML family, OCaml, Haskell (data types)
- **Chapter 16 (HoTT)**: Cubical Agda, RedTT, cooltt, Arend

**Implementation Techniques (Chapters 17-22):**
- **Chapter 17 (Abstract Machines)**: Compiler backends, interpreters, VMs
- **Chapter 18 (NbE)**: Agda, Lean, modern proof assistants
- **Chapter 19 (Bidirectional)**: Agda, Idris, GHC, modern type checkers
- **Chapter 20 (Denotational)**: Language specification, semantics research
- **Chapter 21 (Module Systems)**: OCaml, SML, Rust (modules), Haskell (modules)
- **Chapter 22 (Constraint Inference)**: GHC, rustc, Scala 3, modern compilers

## Prerequisites

### Required

✅ **Basic Programming Experience**
- Comfortable with functions, variables, recursion
- Any language is fine (Python, JavaScript, Java, C++, etc.)

✅ **Basic Math**
- High school algebra
- Understanding of mathematical functions: f(x) = x + 1
- Basic set theory (∈, ⊆) is helpful but not required

### Helpful But Not Required

⚠️ **Functional Programming**
- Familiarity with map, filter, reduce
- Understanding of immutability
- We'll teach you what you need!

⚠️ **Mathematical Logic**
- Propositional logic (∧, ∨, →, ¬)
- Predicate logic (∀, ∃)
- Helps with later chapters but not essential

⚠️ **Programming Language Theory**
- Formal semantics
- Operational semantics
- We explain everything from scratch!

### What You DON'T Need

❌ **Haskell Experience** - We provide a quick-start guide below
❌ **Category Theory** - Not required for this course
❌ **Advanced Math** - No abstract algebra, topology, etc.
❌ **Compiler Experience** - We build from first principles

## Setting Up Your Environment

### Install Stack (Haskell Build Tool)

**macOS:**
```bash
brew install haskell-stack
```

**Linux:**
```bash
curl -sSL https://get.haskellstack.org/ | sh
```

**Windows:**
Download and run: https://get.haskellstack.org/stable/windows-x86_64-installer.exe

### Verify Installation

```bash
stack --version
# Should print: Version 2.x.x or higher
```

### Clone the Repository

```bash
git clone https://github.com/clarissalittler/deptype-course-materials.git
cd deptype-course-materials
```

### Test a Chapter

```bash
cd chapter-01-untyped-lambda
stack build
stack test

# Should see: 57 examples, 0 failures
```

### Editor Setup (Optional but Recommended)

**VS Code:**
1. Install "Haskell" extension
2. Stack will provide language server

**Emacs:**
```elisp
(use-package haskell-mode)
```

**Vim:**
```vim
Plug 'neovimhaskell/haskell-vim'
```

## How to Read This Course

### Structure of Each Chapter

```
chapter-XX-name/
├── README.md              # Start here! Theory and examples
├── src/
│   ├── Syntax.hs         # AST definition
│   ├── TypeCheck.hs      # Type checking (if applicable)
│   ├── Eval.hs           # Evaluator
│   ├── Parser.hs         # Parser (concrete syntax)
│   └── Pretty.hs         # Pretty printer
├── exercises/
│   ├── EXERCISES.md      # Problem descriptions
│   └── Solutions.hs      # Reference solutions (some chapters)
└── test/
    └── Spec.hs           # Test suite
```

### Recommended Learning Path

**For Each Chapter:**

1. **Read README.md** (30-60 minutes)
   - Understand motivation and examples
   - Don't worry if formal rules seem abstract
   - Focus on intuition first

2. **Study src/Syntax.hs** (15 minutes)
   - See how syntax is represented
   - Understand the data types

3. **Experiment with REPL/Tests** (20 minutes)
   - Run `stack test`
   - Try modifying examples
   - See what breaks

4. **Read Implementation** (1-2 hours)
   - Start with TypeCheck.hs or Eval.hs
   - Follow the code, compare with README
   - Add print statements to understand flow

5. **Attempt Exercises** (2-4 hours)
   - Start with "Easy" problems
   - Don't peek at solutions immediately!
   - Struggling is part of learning

6. **Review Solutions** (30 minutes)
   - Compare your approach with reference
   - Understand alternative strategies
   - Note patterns and idioms

### Learning Strategies

**The "Pomodoro" Approach:**
- 25 minutes focused study
- 5 minute break
- Prevents burnout on dense material

**The "Teach-Back" Method:**
- After each section, explain it out loud
- Pretend you're teaching a friend
- Gaps in understanding become obvious

**The "Code-Along" Strategy:**
- Don't just read code, type it!
- Modify examples
- Break things intentionally
- Fix them

**The "Question Everything" Mindset:**
- Why this design choice?
- What if we changed X?
- How does this connect to Y?

## Reading Formal Notation

Don't let mathematical notation intimidate you! Here's how to read the common patterns:

### Inference Rules

```
Premise1    Premise2    Premise3
──────────────────────────────── Rule-Name
        Conclusion
```

**Read as:** "If Premise1 AND Premise2 AND Premise3 are all true, then we can conclude Conclusion"

**Example:**
```
Γ ⊢ t₁ : Bool    Γ ⊢ t₂ : τ    Γ ⊢ t₃ : τ
────────────────────────────────────────── T-If
         Γ ⊢ if t₁ then t₂ else t₃ : τ
```

**In English:** "If `t₁` has type `Bool`, and `t₂` has type `τ`, and `t₃` has type `τ` (all under environment Γ), then the whole if-expression has type `τ`"

### Common Symbols

| Symbol | Meaning | Example |
|--------|---------|---------|
| `Γ` (Gamma) | Type environment | `Γ = {x:Nat, y:Bool}` |
| `⊢` | "proves" or "has type" | `Γ ⊢ t : τ` |
| `→` | Function type | `Nat → Bool` |
| `⇒` | Evaluates to | `t ⇒ v` |
| `≡` | Definitionally equal | `2 + 2 ≡ 4` |
| `∀` | "for all" | `∀α. α → α` |
| `∃` | "there exists" | `∃x. x > 5` |
| `λ` (lambda) | Function | `λx. x + 1` |
| `Π` (Pi) | Dependent function | `Π(n:Nat). Vec n` |
| `Σ` (Sigma) | Dependent pair | `Σ(n:Nat). Vec n` |
| `:=` | Substitution | `t[x := v]` |
| `∈` | "in" or "member of" | `x ∈ Γ` |

### Substitution Notation

`t[x := s]` means "substitute `s` for `x` in `t`"

**Example:**
- `(λy. x + y)[x := 5]` becomes `λy. 5 + y`
- Replace every free `x` with `5`

### Metavariables

Variables that stand for "any term/type":
- `t, t₁, t₂, ...` = any term
- `τ, σ, ...` = any type
- `Γ, Δ, ...` = any environment
- `x, y, z` = any variable name
- `α, β, γ` = any type variable

### Judgment Forms

**Typing judgment:** `Γ ⊢ t : τ`
- Read: "Under environment Γ, term t has type τ"
- Example: `{x:Nat} ⊢ x + 1 : Nat`

**Reduction judgment:** `t → t'`
- Read: "Term t reduces to t' in one step"
- Example: `(λx. x) 5 → 5`

**Multi-step reduction:** `t →* t'`
- Read: "Term t reduces to t' in zero or more steps"

## Haskell Quick Start

You don't need to be a Haskell expert! Here's what you need to know:

### Basic Syntax

```haskell
-- Function definition
add x y = x + y

-- Function application (no parentheses needed!)
result = add 3 4  -- result = 7

-- If expressions (no statements!)
abs x = if x < 0 then -x else x

-- Let bindings
area r =
  let pi = 3.14159
      square x = x * x
  in pi * square r
```

### Data Types

```haskell
-- Algebraic data type
data Bool = True | False

-- Recursive type
data List a = Nil | Cons a (List a)

-- Record type
data Person = Person { name :: String, age :: Int }

-- Pattern matching
length :: List a -> Int
length Nil = 0
length (Cons x xs) = 1 + length xs
```

### Type Signatures

```haskell
-- Read :: as "has type"
add :: Int -> Int -> Int

-- Polymorphic type (works for any type 'a')
identity :: a -> a
identity x = x

-- Type with constraint
sort :: Ord a => [a] -> [a]
```

### Common Patterns in This Course

**AST Definition:**
```haskell
data Term
  = Var String
  | Lam String Type Term
  | App Term Term
  deriving (Eq, Show)
```

**Recursive Functions:**
```haskell
eval :: Term -> Term
eval (Var x) = Var x
eval (App (Lam x _ t) v) = eval (subst x v t)
eval (App t1 t2) = eval (App (eval t1) t2)
eval t = t
```

**Maybe for Errors:**
```haskell
typeOf :: Term -> Maybe Type
typeOf (Var x) = Nothing  -- Free variable has no type
typeOf (Lam x ty t) = Just (TyArr ty (typeOf t))
```

**Either for Error Messages:**
```haskell
typeCheck :: Term -> Either String Type
typeCheck (Var x) = Left ("Unbound variable: " ++ x)
typeCheck (Lam x ty t) = Right (TyArr ty ...)
```

### Resources to Learn More Haskell

- **Learn You a Haskell** (free online): http://learnyouahaskell.com/
- **Haskell Wiki**: https://wiki.haskell.org/
- **99 Haskell Problems**: Good for practice

**But remember:** You can learn Haskell AS you go through this course!

## Study Strategies

### Time Estimates

**Casual Pace:** 2-3 hours per week
- Complete course in ~12-18 months (22 chapters)
- Great for self-study alongside other commitments

**Moderate Pace:** 5-10 hours per week
- Complete course in ~5-6 months
- Suitable for semester-long or year-long independent study

**Intensive Pace:** 20+ hours per week
- Complete course in ~10-12 weeks
- Full-time immersion

### Suggested Schedules

**Weekend Warrior (2 days/week):**
- Saturday: Read theory (2 hours)
- Sunday: Code and exercises (3 hours)
- 1 chapter every 2-3 weeks
- ~44-66 weeks for all 22 chapters

**Daily Learner (1 hour/day):**
- Mon/Wed/Fri: Theory and reading
- Tue/Thu: Coding and exercises
- Weekends: Review and experiments
- 1 chapter per week
- ~22 weeks for all chapters

**Bootcamp Style (40 hours/week):**
- Week 1: Chapters 1-2 (Untyped, Simply Typed)
- Week 2: Chapters 3-4 (ADTs, Hindley-Milner)
- Week 3: Chapters 5-6 (System F, F-omega)
- Week 4: Chapters 7-8 (Dependent Types, Full Dependent)
- Week 5: Chapters 9-10 (Subtyping, Linear Types)
- Week 6: Chapters 11-12 (Refinement Types, Effects)
- Week 7: Chapters 13-14 (Gradual Typing, Row Types)
- Week 8: Chapters 15-16 (Recursive Types, HoTT)
- Week 9: Chapters 17-18 (Abstract Machines, NbE)
- Week 10: Chapters 19-20 (Bidirectional, Denotational)
- Week 11: Chapters 21-22 (Modules, Constraints)

### When You Get Stuck

**Strategies:**

1. **Take a Break**
   - Step away for 15 minutes
   - Come back with fresh eyes
   - Rubber duck debugging works!

2. **Simplify**
   - Make the problem smaller
   - Test individual functions
   - Add print statements

3. **Review Fundamentals**
   - Go back to previous chapters
   - Review the glossary
   - Re-read related sections

4. **Ask for Help**
   - Check GitHub issues/discussions
   - Stack Overflow with `[haskell]` tag
   - Reddit: r/haskell, r/ProgrammingLanguages

5. **Skip and Return**
   - Some problems need time to "marinate"
   - Move forward, come back later
   - The next chapter might provide insight!

### Common Pitfalls

❌ **Skipping Theory**
- Don't just copy code without understanding
- Theory provides the "why"

❌ **Rushing Through**
- Take time to experiment
- Modify examples
- Break things and fix them

❌ **Not Doing Exercises**
- Reading ≠ Learning
- You must code to internalize

❌ **Perfectionism**
- Don't need to master everything before moving on
- Understanding deepens with time
- It's OK to be confused!

✅ **Best Practices:**
- Code along with examples
- Attempt exercises before looking at solutions
- Take notes in your own words
- Explain concepts to others (or yourself!)
- Build your own examples

## What's Next?

Ready to begin? Here's your path forward:

### Chapter Selection Guide

**Choose Your Starting Point:**

**Complete Beginner** (never seen lambda calculus):
→ Start with **Chapter 1: Untyped Lambda Calculus**

**Some PL Theory** (know what lambda calculus is):
→ Start with **Chapter 2: Simply Typed Lambda Calculus**

**Experienced** (comfortable with type systems):
→ Jump to **Chapter 4: Hindley-Milner** or **Chapter 5: System F**

**Researcher/Expert** (interested in dependent types):
→ Jump to **Chapter 7: Dependent Types**

**Interested in Practical Type Features:**
→ Jump to **Chapter 9: Subtyping** (OOP-style types)
→ Jump to **Chapter 10: Linear Types** (Rust-style ownership)
→ Jump to **Chapter 11: Refinement Types** (Liquid Haskell-style)
→ Jump to **Chapter 13: Gradual Typing** (TypeScript-style)

**Interested in Implementation Techniques:**
→ Jump to **Chapter 17: Abstract Machines** (VM/interpreter design)
→ Jump to **Chapter 18: Normalization by Evaluation** (modern normalization)
→ Jump to **Chapter 19: Bidirectional Typing** (practical type checking)
→ Jump to **Chapter 22: Constraint Inference** (modern compilers)

**Interested in Theory/Research:**
→ Jump to **Chapter 16: Homotopy Type Theory** (cutting-edge foundations)
→ Jump to **Chapter 20: Denotational Semantics** (mathematical foundations)
→ Jump to **Chapter 21: Module Systems** (large-scale programming)

### First Steps

1. **Read the main [README.md](README.md)** for course overview
2. **Browse [GLOSSARY.md](GLOSSARY.md)** to familiarize with terms
3. **Choose your starting chapter** from above
4. **Set up your environment** (if you haven't already)
5. **Dive in!**

### Learning Resources

**Books:**
- **Types and Programming Languages** (Pierce) - THE textbook on type systems
- **Practical Foundations for Programming Languages** (Harper)
- **Lambda Calculus: Its Syntax and Semantics** (Barendregt)

**Online:**
- **Software Foundations** (Coq-based course): https://softwarefoundations.cis.upenn.edu/
- **Programming Language Foundations in Agda**: https://plfa.github.io/
- **Oregon Programming Languages Summer School**: https://www.cs.uoregon.edu/research/summerschool/

**Papers:**
Each chapter references foundational papers - read them for deeper understanding!

## Getting Help

**GitHub Issues:** Report bugs, ask questions
**Discussions:** General discussion and Q&A

**Remember:** Everyone struggles with this material at first. Persistence pays off!

---

## Ready?

Now that you're prepared, choose your starting chapter and begin the journey through 22 chapters of type system implementation:

**Core Track:** Chapters 1-8 take you from untyped lambda calculus to full dependent types
**Applied Track:** Chapters 9-16 explore practical type system features used in modern languages
**Implementation Track:** Chapters 17-22 teach you how type systems are implemented in real compilers

**Good luck, and enjoy the adventure!**

---

*Next: [Main README](README.md) | [Chapter 1: Untyped Lambda Calculus](chapter-01-untyped-lambda/README.md)*
