# Troubleshooting Guide

This guide helps you diagnose and fix common errors you'll encounter while working through the course.

## Table of Contents

1. [Build Errors](#build-errors)
2. [Type Errors](#type-errors)
3. [Runtime Errors](#runtime-errors)
4. [REPL Issues](#repl-issues)
5. [Test Failures](#test-failures)
6. [Environment Issues](#environment-issues)

---

## Build Errors

### "Could not find module"

```
error: Could not find module 'Syntax'
```

**Cause**: You're not in the right directory, or the project hasn't been built.

**Fix**:
```bash
# Make sure you're in the chapter directory
cd chapter-01-untyped-lambda

# Initialize and build
stack build
```

### "No .cabal file found"

```
No .cabal file found in directory
```

**Cause**: Stack hasn't been initialized in this directory.

**Fix**:
```bash
stack init
stack build
```

### "Resolver mismatch"

```
Resolver mismatch: resolver in stack.yaml doesn't match
```

**Cause**: Conflicting resolver versions.

**Fix**:
```bash
# Delete lock file and rebuild
rm stack.yaml.lock
stack build
```

### "Package not found in snapshot"

```
In the dependencies for chapter-X:
    package-name needed, but the Stack configuration has no specified version
```

**Cause**: A dependency isn't in the LTS snapshot.

**Fix**: Add to `stack.yaml`:
```yaml
extra-deps:
  - package-name-version
```

---

## Type Errors

### "Couldn't match expected type"

```
Couldn't match expected type 'Type' with actual type 'Term'
```

**What it means**: You're using a value of one type where another is expected.

**Example**:
```haskell
-- Wrong: passing a Term where Type is expected
typeOf ctx (Var x)  -- if ctx expects Type, not Term
```

**Debug steps**:
1. Check the function signature
2. Verify your arguments match expected types
3. Look at what you're passing vs. what's expected

**Common in this course**:
- Confusing `Term` and `Type` in type checker
- Mixing up `Var` (variable name) and `Term` (syntax tree node)

### "Couldn't match type 'a' with 'b'"

```
Couldn't match type 'String' with 'Text'
```

**Cause**: Using incompatible string types.

**Fix**: Convert explicitly:
```haskell
import Data.Text (pack, unpack)

-- String to Text
pack "hello"

-- Text to String
unpack someText
```

### "No instance for (Show Term)"

```
No instance for (Show Term) arising from a use of 'print'
```

**Cause**: Trying to print a type without a Show instance.

**Fix**: Derive or add Show:
```haskell
data Term = ...
  deriving (Show, Eq)
```

Or use the pretty printer:
```haskell
import Pretty (prettyTerm)
putStrLn $ prettyTerm myTerm
```

### "Infinite type" / "Occurs check"

```
Occurs check: cannot construct the infinite type: a ~ a -> b
```

**What it means**: GHC detected a type that would be infinitely recursive.

**Common causes in this course**:
1. Self-application: `\x -> x x` doesn't type in STLC
2. Incorrect recursive type definitions
3. Missing type annotations in polymorphic code

**Example**:
```haskell
-- This won't work - x would need type (a -> b) AND a
badTerm = Lam "x" $ App (Var "x") (Var "x")
```

**Fix**: This is usually intentional in the course! Self-application doesn't type check in simply-typed systems. If you see this in your Haskell code (not the object language), you have a logic error.

### "Ambiguous type variable"

```
Ambiguous type variable 'a0' arising from a use of 'read'
```

**Cause**: GHC can't infer which type you want.

**Fix**: Add type annotation:
```haskell
-- Wrong
let x = read "5"

-- Right
let x = read "5" :: Int
```

### "Non-exhaustive patterns"

```
Pattern match(es) are non-exhaustive
In an equation for 'eval': Patterns not matched: (TmApp _ _)
```

**Cause**: Your pattern match doesn't cover all constructors.

**Fix**: Add missing cases:
```haskell
eval (Var x) = ...
eval (Lam x t) = ...
eval (App t1 t2) = ...  -- Add this!
```

**Tip**: Use `-Wall` to catch these at compile time:
```bash
stack build --ghc-options="-Wall"
```

---

## Runtime Errors

### "Non-exhaustive patterns in function"

```
*** Exception: src/Eval.hs:42:1-30: Non-exhaustive patterns in function step
```

**Cause**: Runtime pattern match failure.

**Debug**:
```haskell
-- Add a catch-all with error message
eval term = case term of
  Var x -> ...
  Lam x t -> ...
  App t1 t2 -> ...
  other -> error $ "Unexpected term: " ++ show other
```

### "Variable not in scope"

At runtime (in REPL):
```
Error: Variable 'x' not found in context
```

**Cause**: Using an unbound variable.

**Fix**: Make sure variables are defined:
```
> let id = \x. x in id y
Error: Variable 'y' not found

> let id = \x. x in let y = 5 in id y
5
```

### "Stack overflow"

```
*** Exception: stack overflow
```

**Cause**: Infinite recursion, often from:
1. Y combinator evaluation without proper strategy
2. Missing base case in recursive function
3. Strict evaluation of infinite structure

**Fix**:
- Check your evaluation strategy (CBV vs CBN)
- Add step limits in your evaluator
- Use `seq` or bang patterns to force evaluation order

---

## REPL Issues

### "Parse error"

```
Parse error at line 1, column 5: unexpected '.'
```

**Common causes**:
1. Missing backslash for lambda: `\x. x` not `λx. x` (unless your parser supports it)
2. Mismatched parentheses
3. Missing spaces: `\x.x` might need to be `\x. x`

**Fix**: Check the REPL_GUIDE.md for your chapter's exact syntax.

### "Type error in REPL"

```
> succ true
Type error: Expected Nat, got Bool
```

**What it means**: Your term doesn't type check.

**This is expected!** The type system is rejecting ill-typed programs. Check:
1. Are your types compatible?
2. Did you forget a type annotation?
3. Is this exercise about understanding why something doesn't type?

### "Command not recognized"

```
Unknown command: :type
```

**Fix**: Check available commands:
```
> :help
```

Common commands vary by chapter:
- `:type <term>` or `:t <term>` - show type
- `:eval <term>` or `:e <term>` - evaluate
- `:parse <term>` or `:p <term>` - show AST
- `:quit` or `:q` - exit

---

## Test Failures

### "expected: X but got: Y"

```
expected: Right (TyArr TyNat TyNat)
 but got: Right (TyArr TyBool TyNat)
```

**Cause**: Your implementation produces different output than expected.

**Debug**:
1. Read the test to understand what's expected
2. Trace through your code manually
3. Add debug prints:
```haskell
import Debug.Trace
myFunction x = trace ("input: " ++ show x) $ ...
```

### "Test timed out"

```
Test suite timed out
```

**Cause**: Infinite loop in your code.

**Common causes**:
1. Non-terminating reduction (e.g., omega combinator)
2. Missing base case
3. Wrong evaluation strategy

**Fix**: Add step limits or check termination conditions.

### Running specific tests

```bash
# Run all tests
stack test

# Run tests matching a pattern
stack test --test-arguments "--match Exercises"
stack test --test-arguments "--match TypeCheck"

# Run with verbose output
stack test --test-arguments "--verbose"
```

---

## Environment Issues

### GHC Version Mismatch

```
The Haskell Tool Stack requires GHC version >= 9.0
```

**Fix**:
```bash
# Let Stack manage GHC
stack setup

# Check version
stack ghc -- --version
```

### Stack Not Found

```
stack: command not found
```

**Fix**: Install Stack:
```bash
# macOS
brew install haskell-stack

# Linux
curl -sSL https://get.haskellstack.org/ | sh

# Windows
# Download from https://www.haskellstack.org/
```

### Permission Denied

```
Permission denied: ~/.stack/...
```

**Fix**:
```bash
# Fix permissions
sudo chown -R $(whoami) ~/.stack

# Or use a different Stack root
export STACK_ROOT=~/my-stack
```

### Memory Issues

```
ghc: out of memory
```

**Fix**: Increase memory limits:
```bash
stack build --ghc-options="+RTS -M4G -RTS"
```

Or in `package.yaml`:
```yaml
ghc-options:
  - +RTS -M4G -RTS
```

---

## Debugging Strategies

### 1. Isolate the Problem

```haskell
-- Test components separately
testParser = parse "\\x. x"
testTypeCheck = typeOf emptyCtx (Lam "x" TyNat (Var "x"))
testEval = eval (App (Lam "x" TyNat (Var "x")) TmZero)
```

### 2. Add Tracing

```haskell
import Debug.Trace

eval term = trace ("Evaluating: " ++ show term) $
  case term of
    ...
```

### 3. Use GHCi

```bash
stack ghci

# Load a module
:load src/TypeCheck.hs

# Test interactively
> typeOf emptyCtx (Var "x")
```

### 4. Check Types

```bash
# In GHCi
:type myFunction
:info MyType
```

### 5. Read Error Messages Carefully

GHC error messages contain valuable info:
- **Expected type**: What GHC wanted
- **Actual type**: What you provided
- **In the expression**: Which code caused it
- **Relevant bindings**: What's in scope

---

## Getting Help

### Before Asking

1. Read the error message completely
2. Check this troubleshooting guide
3. Search the error message online
4. Review relevant chapter materials
5. Try to create a minimal example

### Where to Ask

- Stack Overflow: Tag with `[haskell]` and `[type-systems]`
- Haskell Discourse: https://discourse.haskell.org
- Reddit: r/haskell

### What to Include

1. Full error message
2. Minimal code that reproduces the issue
3. GHC/Stack version (`stack --version`, `stack ghc -- --version`)
4. What you expected vs. what happened
5. What you've already tried

---

## Quick Reference: Error → Solution

| Error | Likely Cause | Quick Fix |
|-------|--------------|-----------|
| "Could not find module" | Wrong directory | `cd chapter-XX && stack build` |
| "Couldn't match type" | Type mismatch | Check function signatures |
| "Infinite type" | Self-application or recursion | Usually expected; check logic |
| "Non-exhaustive patterns" | Missing case | Add all constructors |
| "Variable not in scope" | Typo or unbound var | Check spelling and scope |
| "Parse error" | Syntax issue | Check REPL_GUIDE.md |
| "Stack overflow" | Infinite recursion | Add step limits |
| "No instance for Show" | Missing instance | Add `deriving Show` |

---

**Remember**: Errors are learning opportunities! Each one teaches you something about the type system you're implementing.
