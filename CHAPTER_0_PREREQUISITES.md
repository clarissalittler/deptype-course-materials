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

This course teaches you to **implement type systems from scratch**. You'll build 8 different type checkers and evaluators, each more sophisticated than the last:

```
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
```

**By the end**, you'll understand the foundations of:
- Programming language design
- Type checking and inference
- Proof assistants (Coq, Agda, Lean)
- Verified programming

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

- **Chapter 1-2 (STLC)**: C, Java, Go, TypeScript (basic mode)
- **Chapter 4 (Hindley-Milner)**: Haskell, OCaml, F#, Rust (inference)
- **Chapter 5 (System F)**: Haskell (under the hood), Java generics
- **Chapter 6 (F-omega)**: Haskell type families, Scala higher-kinded types
- **Chapter 7-8 (Dependent Types)**: Agda, Coq, Idris, Lean

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
- Complete course in ~6 months
- Great for self-study alongside other commitments

**Moderate Pace:** 5-10 hours per week
- Complete course in ~2 months
- Suitable for semester-long independent study

**Intensive Pace:** 20+ hours per week
- Complete course in ~3-4 weeks
- Full-time immersion

### Suggested Schedules

**Weekend Warrior (2 days/week):**
- Saturday: Read theory (2 hours)
- Sunday: Code and exercises (3 hours)
- 1 chapter every 2-3 weeks

**Daily Learner (1 hour/day):**
- Mon/Wed/Fri: Theory and reading
- Tue/Thu: Coding and exercises
- Weekends: Review and experiments
- 1 chapter per week

**Bootcamp Style (40 hours/week):**
- Week 1: Chapters 1-2
- Week 2: Chapters 3-4
- Week 3: Chapters 5-6
- Week 4: Chapters 7-8

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

Now that you're prepared, choose your starting chapter and begin the journey from untyped lambda calculus to full dependent types!

**Good luck, and enjoy the adventure!** 🚀

---

*Next: [Main README](README.md) | [Chapter 1: Untyped Lambda Calculus](chapter-01-untyped-lambda/README.md)*
