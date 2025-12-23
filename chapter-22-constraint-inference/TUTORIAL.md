# Tutorial: Implementing Constraint-Based Type Inference

This tutorial walks through implementing constraint-based type inference step by step.

## Overview: The Two-Phase Approach

Constraint-based type inference has two phases:

1. **Phase 1 - Constraint Generation**: Walk the AST and generate constraints
2. **Phase 2 - Constraint Solving**: Solve constraints using unification

Let's implement each phase!

## Step 1: Define Constraints

First, we need to represent constraints:

```haskell
data Constraint
  = Equal Type Type    -- τ₁ ≡ τ₂
  deriving (Eq, Show)

type ConstraintSet = [Constraint]
```

For basic Hindley-Milner, we only need **equality constraints**.

## Step 2: Fresh Variable Generation

We need fresh type variables to avoid accidental sharing:

```haskell
newtype ConstraintGen a = ConstraintGen
  (ExceptT ConstraintError (State Int) a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadError ConstraintError)

fresh :: ConstraintGen Type
fresh = do
  n <- get
  put (n + 1)
  return $ TyVar ("t" ++ show n)
```

Each call to `fresh` returns a unique type variable.

## Step 3: Constraint Generation - Variables

Variables are looked up in the environment and **instantiated**:

```haskell
generateConstraints :: TypeEnv -> Term -> ConstraintGen (ConstraintSet, Type)
generateConstraints env (Var x) = case lookup x env of
  Nothing -> throwError (UnboundVariable x)
  Just scheme -> do
    ty <- instantiate scheme
    return ([], ty)    -- No constraints needed!
```

**Instantiation** replaces bound type variables with fresh ones:

```haskell
instantiate :: TypeScheme -> ConstraintGen Type
instantiate (TypeScheme vars ty) = do
  freshVars <- mapM (const fresh) vars
  let subst = Map.fromList (zip vars freshVars)
  return $ applySubst subst ty
```

## Step 4: Constraint Generation - Lambda

For `λx. e`, we:
1. Generate a fresh type variable for `x`
2. Generate constraints for the body
3. Return the function type

```haskell
generateConstraints env (Lam x body) = do
  tyVar <- fresh                            -- Fresh type for x
  let env' = extendEnv x (TypeScheme [] tyVar) env
  (constraints, bodyTy) <- generateConstraints env' body
  return (constraints, TyArr tyVar bodyTy)  -- x : tyVar → bodyTy
```

**No new constraints!** The constraint comes from how `x` is used in the body.

## Step 5: Constraint Generation - Application

For `e₁ e₂`, we:
1. Generate constraints for `e₁` and `e₂`
2. Create a fresh type variable for the result
3. Add a constraint that `e₁` must be a function

```haskell
generateConstraints env (App t1 t2) = do
  (c1, ty1) <- generateConstraints env t1
  (c2, ty2) <- generateConstraints env t2
  resultTy <- fresh
  let constraint = Equal ty1 (TyArr ty2 resultTy)
  return (c1 ++ c2 ++ [constraint], resultTy)
```

**Key insight**: We don't know what type `e₁` has, but we know it must be a function from `ty2` to some result type!

## Step 6: Constraint Generation - If

For `if e₁ then e₂ else e₃`, we:
1. Generate constraints for all three subexpressions
2. Constrain condition to be `Bool`
3. Constrain branches to have the same type

```haskell
generateConstraints env (TmIf t1 t2 t3) = do
  (c1, ty1) <- generateConstraints env t1
  (c2, ty2) <- generateConstraints env t2
  (c3, ty3) <- generateConstraints env t3
  let constraints = c1 ++ c2 ++ c3 ++
                    [Equal ty1 TyBool, Equal ty2 ty3]
  return (constraints, ty2)
```

## Step 7: Constraint Generation - Let

For `let x = e₁ in e₂`, we use **let-polymorphism**:

```haskell
generateConstraints env (Let x t1 t2) = do
  (c1, ty1) <- generateConstraints env t1
  -- Generalize ty1 (this is key to polymorphism!)
  let scheme = generalize env ty1
      env' = extendEnv x scheme env
  (c2, ty2) <- generateConstraints env' t2
  return (c1 ++ c2, ty2)
```

**Generalization** introduces ∀:

```haskell
generalize :: TypeEnv -> Type -> TypeScheme
generalize env ty =
  let vars = Set.toList (freeTyVars ty Set.\\ freeTyVarsEnv env)
  in TypeScheme vars ty
```

## Step 8: Unification

Now we need to **solve** the constraints using unification:

```haskell
unify :: Type -> Type -> Either SolveError Subst
unify t1 t2 | t1 == t2 = return emptySubst
unify (TyVar a) t = bindVar a t
unify t (TyVar a) = bindVar a t
unify (TyArr t1 t2) (TyArr t1' t2') = do
  s1 <- unify t1 t1'
  s2 <- unify (applySubst s1 t2) (applySubst s1 t2')
  return (s2 `composeSubst` s1)
unify t1 t2 = throwError $ UnificationFail t1 t2
```

**Key steps**:
1. If types are identical: no substitution needed
2. If one is a variable: bind it (with occurs check!)
3. If both are functions: unify components recursively
4. Otherwise: fail

## Step 9: Occurs Check

Before binding a variable, check it doesn't occur in the type:

```haskell
bindVar :: TyVar -> Type -> Either SolveError Subst
bindVar a t
  | t == TyVar a = return emptySubst
  | a `Set.member` freeTyVars t = throwError $ OccursCheck a t
  | otherwise = return $ Map.singleton a t
```

This prevents infinite types like `α = α → β`.

## Step 10: Constraint Solving

Solve a set of constraints by unifying each one:

```haskell
solve :: ConstraintSet -> Either SolveError Subst
solve = solveConstraints emptySubst
  where
    solveConstraints s [] = return s
    solveConstraints s (Equal t1 t2 : cs) = do
      let t1' = applySubst s t1  -- Apply previous substitutions!
      let t2' = applySubst s t2
      s' <- unify t1' t2'
      solveConstraints (s' `composeSubst` s) cs
```

**Important**: Always apply accumulated substitutions before unifying!

## Step 11: Full Inference

Combine generation and solving:

```haskell
inferType :: Term -> Either InferenceError (ConstraintSet, Subst, Type)
inferType t = do
  -- Phase 1: Generate constraints
  (constraints, ty) <- case generateConstraints emptyEnv t of
    Left err -> Left (ConstraintErr err)
    Right res -> Right res

  -- Phase 2: Solve constraints
  subst <- case solve constraints of
    Left err -> Left (SolveErr err)
    Right s -> Right s

  -- Apply substitution to get final type
  let finalType = applySubst subst ty
  return (constraints, subst, finalType)
```

## Step 12: Pretty Printing

For debugging, pretty-print constraints:

```haskell
prettyConstraint :: Constraint -> String
prettyConstraint (Equal t1 t2) = prettyType t1 ++ " ≡ " ++ prettyType t2

prettyConstraints :: ConstraintSet -> String
prettyConstraints cs = unlines $ map prettyConstraint cs
```

## Example Walkthrough

Let's trace `λf. λx. f x`:

### Phase 1: Constraint Generation

```
1. Generate fresh α for f
   env = {f : α}

2. Generate fresh β for x
   env = {f : α, x : β}

3. Generate constraints for f x:
   - f has type α (lookup)
   - x has type β (lookup)
   - Create fresh γ for result
   - Add constraint: α ≡ β → γ

4. Result:
   Constraints: {α ≡ β → γ}
   Type: α → β → γ
```

### Phase 2: Constraint Solving

```
Solve α ≡ β → γ:
  bindVar α (β → γ)
  Occurs check: α ∉ ftv(β → γ) ✓
  Substitution: {α ↦ β → γ}

Apply to type:
  α → β → γ [α ↦ β → γ]
  = (β → γ) → β → γ

Final type: (t1 → t2) → t1 → t2
```

**Rename for clarity**: `(a → b) → a → b`

This is the type of function application!

## Testing Your Implementation

Use the REPL to test:

```haskell
-- Test identity
λ> :solve \x. x
Generated constraints:
  (no constraints)
Final type: t0 -> t0

-- Test with constraints
λ> :solve \x. succ x
Generated constraints:
  t1 ≡ Nat
Solved with substitution:
  {t1 ↦ Nat}
Final type: Nat -> Nat

-- Test let-polymorphism
λ> :solve let id = \x. x in (id 0, id true)
Generated constraints:
  t2 ≡ Nat
  t4 ≡ Bool
Final type: Nat * Bool
```

## Common Mistakes

### Mistake 1: Not using fresh variables

```haskell
-- WRONG: Reusing the same type variable
Lam "x" (Lam "y" ...)  -- both x and y get α? NO!

-- RIGHT: Fresh variable for each binding
do
  alphaX <- fresh
  alphaY <- fresh
  ...
```

### Mistake 2: Not applying substitutions

```haskell
-- WRONG: Solving without applying previous substitutions
solveConstraints s (c:cs) = do
  s' <- unify t1 t2  -- Using original types!
  solveConstraints (s' `composeSubst` s) cs

-- RIGHT: Apply accumulated substitution first
solveConstraints s (Equal t1 t2:cs) = do
  let t1' = applySubst s t1  -- Apply s first!
  let t2' = applySubst s t2
  s' <- unify t1' t2'
  solveConstraints (s' `composeSubst` s) cs
```

### Mistake 3: Forgetting occurs check

```haskell
-- WRONG: Binding without occurs check
bindVar a t = return $ Map.singleton a t  -- Allows α = α → β!

-- RIGHT: Check first
bindVar a t
  | a `Set.member` freeTyVars t = throwError $ OccursCheck a t
  | otherwise = return $ Map.singleton a t
```

## Extensions

Now that you have basic constraint-based inference, you can easily add:

### Extension 1: Subtyping

```haskell
data Constraint
  = Equal Type Type
  | Subtype Type Type    -- τ₁ <: τ₂

-- Add rules for subtype solving
```

### Extension 2: Type Classes

```haskell
data Constraint
  = Equal Type Type
  | InstanceOf TypeClass Type    -- Show τ

-- Resolve instances during constraint solving
```

### Extension 3: Effects

```haskell
data Constraint
  = Equal Type Type
  | HasEffect Term Effect    -- e performs IO

-- Track effects through computation
```

## Next Steps

1. **Implement the basic system** - follow this tutorial
2. **Test thoroughly** - use the provided test suite
3. **Compare with Algorithm W** (Chapter 4) - understand the differences
4. **Try the exercises** - extend with new features
5. **Read the papers** - understand theoretical foundations

## Resources

- **README.md**: Detailed theory and examples
- **FAQ.md**: Answers to common questions
- **EXERCISES.md**: Practice problems
- **Solutions.hs**: Reference implementations

Happy hacking! 🚀
