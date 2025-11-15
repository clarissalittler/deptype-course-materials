# REPL Implementation Status

## Overview

Interactive REPLs (Read-Eval-Print Loops) provide hands-on exploration of type systems, essential for understanding evaluation strategies, type checking, and type inference.

## Completed REPLs ✅

### Chapter 1: Untyped Lambda Calculus REPL ✅

**Status**: Fully implemented and tested

**Location**: `chapter-01-untyped-lambda/`

**Features**:
- Parse and evaluate untyped lambda terms
- Multiple evaluation strategies (normal order, call-by-value, call-by-name)
- Step-by-step evaluation mode
- Evaluation trace visualization
- Named bindings with `:let`
- Session save/load
- Extensive help and examples (Church encodings, combinators)

**Files**:
- `app/Main.hs` - Entry point
- `app/REPL.hs` - Full implementation (340+ lines)
- `REPL_GUIDE.md` - Complete user guide (600+ lines)

**Usage**:
```bash
cd chapter-01-untyped-lambda
stack build
stack exec untyped-lambda-repl
```

**Example Session**:
```
λ> \x. x
  λx. x

λ> :let id = \x. x
  id = λx. x

λ> :let true = \t f. t
  true = λt f. t

λ> :strategy cbv
Evaluation strategy: Call-by-value

λ> :step
Step mode enabled

λ> (\x. x x) (\y. y)
  (λx. x x) (λy. y)
    [Press Enter]
→ (λy. y) (λy. y)
    [Press Enter]
→ λy. y
```

### Chapter 2: Simply Typed Lambda Calculus REPL ✅

**Status**: Fully implemented and tested

**Location**: `chapter-02-simply-typed-lambda/`

**Features**:
- Parse and evaluate typed lambda terms
- Automatic type checking before evaluation
- Type inference and type display
- Type query command (`:type`)
- Step-by-step evaluation mode
- Evaluation trace visualization
- Named bindings with type tracking
- Session save/load
- Detailed type error messages
- Toggle type checking on/off

**Files**:
- `app/Main.hs` - Entry point
- `app/REPL.hs` - Full typed REPL implementation (460+ lines)

**Usage**:
```bash
cd chapter-02-simply-typed-lambda
stack build
stack exec simply-typed-lambda-repl
```

**Example Session**:
```
λ> \x:Bool. if x then false else true
  : Bool -> Bool
  λx:Bool. if x then false else true

λ> :type \f:Nat->Nat. \x:Nat. f (f x)
  \f:Nat->Nat. \x:Nat. f (f x) : (Nat -> Nat) -> Nat -> Nat

λ> :let twice = \f:Nat->Nat. \x:Nat. f (f x)
  twice : (Nat -> Nat) -> Nat -> Nat
  twice = λf:Nat->Nat. λx:Nat. f (f x)

λ> twice (\x:Nat. succ x) 0
  : Nat
  succ (succ 0)

λ> (\\x:Bool. x) 0
Type error: Argument type mismatch: expected Bool but got Nat
```

## Implementation Architecture

### Common REPL Structure

All REPLs follow a consistent architecture:

```haskell
data REPLState = REPLState
  { termBindings :: Map String Term
  , typeBindings :: Map String Type      -- For typed calculi
  , stepMode :: Bool
  , showSteps :: Bool
  , showTypes :: Bool
  , maxSteps :: Int
  -- Chapter-specific settings...
  }

runREPL :: IO ()
runREPL = do
  showWelcome
  loop initialState

loop :: REPLState -> IO ()
loop state = do
  prompt
  input <- getLine
  case input of
    ':':cmd -> handleCommand cmd state
    _       -> handleTerm input state
```

### Core Commands (Common to All REPLs)

| Command | Description |
|---------|-------------|
| `:help`, `:h`, `:?` | Show help |
| `:quit`, `:q`, `:exit` | Exit REPL |
| `:examples`, `:ex` | Show examples |
| `:bindings`, `:b` | Show bindings |
| `:clear`, `:c` | Clear bindings |
| `:step` / `:nostep` | Toggle step mode |
| `:trace` / `:notrace` | Toggle trace mode |
| `:let name = term` | Define binding |
| `:load file` | Load session |
| `:save file` | Save session |

### Type System Commands (Typed Calculi)

| Command | Description |
|---------|-------------|
| `:type term` | Query term type |
| `:types` / `:notypes` | Show/hide types |
| `:typecheck` / `:notypecheck` | Enable/disable checking |

## Remaining REPLs

### Chapter 3: STLC with ADTs

**What to Add**:
- Product types: `(t1, t2)`, `fst`, `snd`
- Sum types: `inl[T]`, `inr[T]`, `case`
- Records: `{l1=t1, l2=t2}`, `t.l`
- Variants: `<l=t> as T`, variant case
- Lists: `[]`, `::`, list patterns

**Parser Extensions Needed**:
```haskell
-- Product types
(t1, t2)                -- pair
fst t                   -- projection
snd t                   -- projection

-- Sum types
inl[Bool] true          -- left injection
inr[Nat] 0              -- right injection
case t of inl x => t1 | inr y => t2

-- Records
{name="John", age=30}   -- record literal
person.name             -- projection

-- Variants
<some=5> as <some:Nat, none:Unit>
case v of <some=x> => x | <none=_> => 0

-- Lists
[1, 2, 3]               -- list literal
1 :: [2, 3]             -- cons
case l of [] => 0 | h::t => h
```

**Estimated Effort**: 3-4 hours
- Parser updates: 1 hour
- Pretty printer updates: 30 minutes
- Type display updates: 30 minutes
- Example terms: 1 hour
- Testing: 1 hour

### Chapter 4: Hindley-Milner Type Inference

**What to Add**:
- Automatic type inference (no type annotations needed!)
- Unification algorithm visualization
- Let-polymorphism demonstration
- Type scheme display
- Constraint generation/solving display

**Key Features**:
```
λ> let id = \x. x in id 5
  id : ∀a. a -> a
  5

λ> let compose = \f. \g. \x. f (g x)
  compose : ∀a b c. (b -> c) -> (a -> b) -> a -> c

λ> :infer \f. \g. \x. f (g x)
  Constraints generated:
    τ₁ = τ₂ → τ₃
    τ₄ = τ₅ → τ₂
    ...
  Unification:
    τ₁ ~ τ₂ → τ₃
    ...
  Result: ∀a b c. (b → c) → (a → b) → a → c

λ> :trace-unify
  [Shows step-by-step unification]
```

**Estimated Effort**: 4-5 hours
- Inference display: 2 hours
- Unification trace: 2 hours
- Type scheme pretty printing: 1 hour

### Chapter 5: System F (Polymorphism)

**What to Add**:
- Explicit type abstraction: `ΛA. t`
- Type application: `t [T]`
- Universal types: `∀A. T`
- Church encodings with polymorphism

**Parser Extensions**:
```haskell
/\A. \x:A. x            -- type abstraction (ΛA. λx:A. x)
id [Bool] true          -- type application
```

**Example Session**:
```
λ> :let id = /\A. \x:A. x
  id : ∀A. A -> A

λ> id [Bool] true
  : Bool
  true

λ> id [Nat] 5
  : Nat
  5

λ> :let List = /\A. forall R. R -> (A -> R -> R) -> R
  List : (* -> *) ...
```

**Estimated Effort**: 3-4 hours

### Chapter 6: System F-omega (Higher-Kinded Types)

**What to Add**:
- Kind checking
- Type-level lambdas: `λA::*. T`
- Type-level application
- Kind display: `* -> *`, `(* -> *) -> *`
- Type operator examples

**Example Session**:
```
λ> :kind List
  List : * -> *

λ> :kind /\A::*. /\B::*. A -> B
  (* -> * -> *)

λ> :let Functor = /\F::*->*. ...
  Functor : (* -> *) -> *
```

**Estimated Effort**: 5-6 hours
- Kind checking display: 2 hours
- Type-level computation: 2 hours
- Higher-kinded examples: 2 hours

### Chapter 7: Dependent Types (Basic)

**What to Add**:
- Π types: `Π(x:A). B`
- Σ types: `Σ(x:A). B`
- Dependent function application
- Normalization-based equality
- Vector examples

**Example Session**:
```
λ> :let vec = Π(n:Nat). Type -> Type
  vec : Nat -> Type -> Type

λ> :let replicate = Π(n:Nat). Π(A:Type). A -> Vec n A
  replicate : ...

λ> replicate 3 Bool true
  : Vec 3 Bool
  [true, true, true]
```

**Estimated Effort**: 6-8 hours
- Dependent type display: 3 hours
- Normalization traces: 2 hours
- Vector operations: 3 hours

### Chapter 8: Full Dependent Types

**What to Add**:
- Universe hierarchy display: `Type 0 : Type 1 : ...`
- Equality type checking
- J eliminator
- Inductive families
- Proof term display

**Example Session**:
```
λ> :type Type 0
  Type 0 : Type 1

λ> :let plus-comm = Π(m n : Nat). Eq Nat (m + n) (n + m)
  plus-comm : Π(m : Nat). Π(n : Nat). Eq Nat (m + n) (n + m)

λ> :prove plus-comm 2 3
  [Shows proof steps using J eliminator]
```

**Estimated Effort**: 8-10 hours
- Universe level display: 2 hours
- Equality proofs: 4 hours
- Proof tactics: 4 hours

## Implementation Guide

### Step-by-Step REPL Creation

#### 1. Setup (5 minutes)
```bash
mkdir app
touch app/Main.hs app/REPL.hs
```

Update `package.yaml`:
```yaml
executables:
  <chapter>-repl:
    main: Main.hs
    source-dirs: app
    ghc-options:
    - -threaded
    - -rtsopts
    - -with-rtsopts=-N
    dependencies:
    - <chapter>
```

#### 2. Copy Template (10 minutes)
Start with Chapter 2's REPL as a template for typed calculi, or Chapter 1 for untyped.

#### 3. Customize Parser (30-60 minutes)
Add chapter-specific syntax to term parser.

#### 4. Customize Type Checking (30-60 minutes)
Update type query and type display functions.

#### 5. Add Examples (30 minutes)
Create `showExamples` with chapter-specific demonstrations.

#### 6. Test (30-60 minutes)
```bash
stack build
stack exec <chapter>-repl
```
Test all commands and features.

#### 7. Document (30 minutes)
Create or update `REPL_GUIDE.md`.

### Testing Checklist

For each REPL, verify:
- [ ] Parsing works for all term forms
- [ ] Type checking provides clear errors
- [ ] Evaluation produces correct results
- [ ] Step mode works
- [ ] Trace mode shows all steps
- [ ] Bindings work correctly
- [ ] Save/load preserves state
- [ ] Help displays correctly
- [ ] Examples all work

## Integration with Course

### How REPLs Support Learning

1. **Immediate Feedback**: Students see results instantly
2. **Exploration**: Try variations without writing full programs
3. **Visualization**: Step-by-step mode reveals evaluation
4. **Type Safety**: Type errors explain what went wrong
5. **Examples**: Built-in examples demonstrate concepts

### Recommended Usage

#### For Students:
1. Start with `:examples` to see syntax
2. Try modifying examples
3. Use `:step` to understand evaluation
4. Use `:type` to understand type inference
5. Save interesting sessions with `:save`

#### For Instructors:
1. Live coding demonstrations
2. Show type errors and fixes
3. Compare evaluation strategies
4. Demonstrate Church encodings
5. Build up complex terms incrementally

## Build and Usage Summary

### Quick Start (Any Chapter)
```bash
cd chapter-XX-<name>
stack build
stack exec <name>-repl
```

### Chapters with REPLs
- ✅ Chapter 1: `untyped-lambda-repl`
- ✅ Chapter 2: `simply-typed-lambda-repl`
- ⏳ Chapter 3: `stlc-adt-repl` (planned)
- ⏳ Chapter 4: `hindley-milner-repl` (planned)
- ⏳ Chapter 5: `system-f-repl` (planned)
- ⏳ Chapter 6: `system-f-omega-repl` (planned)
- ⏳ Chapter 7: `dependent-types-repl` (planned)
- ⏳ Chapter 8: `full-dependent-types-repl` (planned)

## Future Enhancements

### Possible REPL Features

1. **Syntax Highlighting**: Color-code terms, types, keywords
2. **Tab Completion**: Complete variable names, commands
3. **History**: Arrow keys for command history (readline)
4. **Multi-line Input**: Handle complex terms over multiple lines
5. **Import System**: Load standard library definitions
6. **Proof Mode**: Interactive proof construction (Chapter 8)
7. **Debugger**: Breakpoints, inspection, backtracking
8. **Web Interface**: Browser-based REPL with visualization

### Visualization Ideas

1. **Evaluation Trees**: Graphical reduction steps
2. **Type Derivations**: Tree display of typing judgments
3. **Unification Steps**: Show constraint solving (Chapter 4)
4. **Proof Trees**: Display proof structure (Chapter 8)
5. **Kind Derivations**: Show kind checking (Chapter 6)

## Technical Notes

### Dependencies

All REPLs use:
- `base` - Haskell standard library
- `containers` - Map, Set data structures
- `text` - Text processing
- `megaparsec` - Parsing
- `mtl` - Monad transformers (for error handling)

### Code Statistics

| Chapter | REPL Lines | Features | Complexity |
|---------|------------|----------|------------|
| 1 | 340 | Basic | Low |
| 2 | 460 | +Type checking | Medium |
| 3 | ~500 | +ADTs | Medium-High |
| 4 | ~550 | +Inference | High |
| 5 | ~500 | +Polymorphism | Medium-High |
| 6 | ~600 | +Kinds | High |
| 7 | ~650 | +Dependent types | Very High |
| 8 | ~700 | +Universes | Very High |

**Total Estimated**: ~4300 lines of REPL code across all chapters

### Performance Considerations

- **Max Steps**: Default 1000 prevents infinite loops
- **Step Limit**: Configurable for complex reductions
- **Lazy Evaluation**: Use sparingly in step mode
- **Memory**: Watch for large Church numerals

## Contributing

### Adding a New REPL

1. Follow the implementation guide above
2. Use existing REPLs as templates
3. Add comprehensive examples
4. Test thoroughly
5. Document all features
6. Update this status document

### Code Style

- Follow existing REPL structure
- Use clear variable names
- Add type signatures
- Comment complex logic
- Provide helpful error messages

## Summary

**Completed**: 2/8 REPLs (Chapters 1-2)
**Progress**: 25% of total REPL implementation
**Lines of Code**: ~800 lines of REPL code
**Estimated Remaining**: ~3500 lines, 30-40 hours

The foundation is solid with two working REPLs demonstrating the pattern. The remaining REPLs follow similar structures with chapter-specific extensions.

## Next Steps

1. Complete Chapter 3 REPL (ADTs)
2. Complete Chapter 4 REPL (Type Inference) - High value for visualization
3. Complete Chapters 5-6 (Polymorphism and Kinds)
4. Complete Chapters 7-8 (Dependent Types) - Most complex
5. Create web-based visualization tools (Task F)
6. Add tab completion and history
7. Create integrated documentation browser

The REPLs provide essential hands-on experience for understanding type systems. Combined with the cheat sheets and real-world connections, students have comprehensive learning resources.
