# Chapter 10: Linear Types - Exercises

## Exercise 1: Linear vs Unrestricted

Determine which of these terms are well-typed. If ill-typed, explain why.

1. `λx :1 Nat. x`
2. `λx :1 Nat. (x, x)`
3. `λx :ω Nat. (x, x)`
4. `λx :1 Nat. 0`
5. `λx :ω Nat. 0`
6. `λx :1 Nat. let y :1 = x in y`

## Exercise 2: Pair Usage

For each expression, determine if it's well-typed:

1. `let (a, b) = (0, true) in a`
2. `let (a, b) = (0, true) in (a, b)`
3. `let (a, b) = (0, true) in (b, a)`
4. `let (a, b) = (0, true) in (a, a)`

## Exercise 3: Bang Types

Explain the role of `!` in each expression:

1. `!0`
2. `let !x = !0 in (x, x)`
3. `λf :1 (!Nat -o Nat). f !0`

Why can't we write `λx :1 Nat. !x`?

## Exercise 4: Implement Swap

Write a function that swaps a pair:

```
swap : (A * B) -o (B * A)
```

Why must this be a linear function?

## Exercise 5: Implement Apply

Write the linear application function:

```
apply : ((A -o B) * A) -o B
```

## Exercise 6: Add Affine Types

Extend the type system with **affine** types (used *at most* once):

- `A -a-> B`: Affine function type
- Affine variables can be used 0 or 1 times

Implement:
1. Add `Affine` to the `Mult` type
2. Update the type checker
3. Add tests

## Exercise 7: Add Relevant Types

Extend with **relevant** types (used *at least* once):

- `A -r-> B`: Relevant function type
- Relevant variables must be used ≥1 times

This combines with affine to give:
- Linear: exactly once (affine + relevant)
- Affine: at most once
- Relevant: at least once
- Unrestricted: any number

## Exercise 8: Session Types

Implement a simple session type system:

```
Session ::= End
          | Send τ Session
          | Recv τ Session
          | Choose Session Session
          | Offer Session Session
```

Key idea: A channel has a session type, and each communication step consumes the channel and returns a new one with the "rest" of the session.

## Challenge Exercises

### Challenge 1: Graded Modal Types

Implement graded modalities where the "bang" can track exact counts:

```
!n A  -- Value can be used exactly n times
!ω A  -- Value can be used any number of times
```

Rules:
- `!0 A` values cannot be used
- `!1 A ≅ A` (isomorphic to linear)
- `!(n+m) A ≅ !n A ⊗ !m A`

### Challenge 2: Fractional Permissions

Implement fractional permissions for shared read access:

```
Ref A         -- Full (unique) access
Ref/2 A       -- Half permission (shared read)
Ref/4 A       -- Quarter permission
```

Rules:
- Can split: `Ref A -o Ref/2 A * Ref/2 A`
- Can join: `Ref/2 A * Ref/2 A -o Ref A`
- Full access needed for write

### Challenge 3: Linear State Monad

Implement a state monad that uses linear types to ensure safe state threading:

```
LState s a = s -o (a, s)

return : a -o LState s a
(>>=) : LState s a -o (a -o LState s b) -o LState s b
get : LState s s
put : s -o LState s ()
```

Key insight: The state is threaded linearly, preventing aliasing.

## References

- Girard, "Linear Logic" (1987)
- Wadler, "Linear Types Can Change the World!" (1990)
- Bernardy et al., "Linear Haskell" (2017)
- Walker, "Substructural Type Systems" (2005)
