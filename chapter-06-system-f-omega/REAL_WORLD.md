# Chapter 6: Real-World Connections

## Higher-Kinded Types in Practice

### Haskell Type Classes

```haskell
-- Functor has kind (* -> *) -> Constraint
class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- f is a type constructor, not a type!
-- f :: * -> *

instance Functor [] where
  fmap = map

instance Functor Maybe where
  fmap f Nothing  = Nothing
  fmap f (Just x) = Just (f x)

instance Functor (Either e) where
  fmap f (Left e)  = Left e
  fmap f (Right x) = Right (f x)
```

### Scala Higher-Kinded Types

```scala
// Functor with higher-kinded type parameter
trait Functor[F[_]] {
  def map[A, B](fa: F[A])(f: A => B): F[B]
}

// F[_] means "a type constructor that takes one type argument"
// F :: * -> *

implicit val listFunctor: Functor[List] = new Functor[List] {
  def map[A, B](fa: List[A])(f: A => B): List[B] = fa.map(f)
}

implicit val optionFunctor: Functor[Option] = new Functor[Option] {
  def map[A, B](fa: Option[A])(f: A => B): Option[B] = fa.map(f)
}
```

### Rust (Simulated via Traits)

```rust
// Rust doesn't have HKTs directly, but GATs help:
trait Functor {
    type F<T>;  // Generic Associated Type

    fn fmap<A, B>(fa: Self::F<A>, f: impl Fn(A) -> B) -> Self::F<B>;
}

// With GATs (stabilized in Rust 1.65)
struct OptionFunctor;
impl Functor for OptionFunctor {
    type F<T> = Option<T>;

    fn fmap<A, B>(fa: Option<A>, f: impl Fn(A) -> B) -> Option<B> {
        fa.map(f)
    }
}
```

---

## Type Constructors as Functions

### TypeScript Mapped Types

```typescript
// Type-level function!
type Nullable<T> = T | null;

// Apply to different types
type MaybeNumber = Nullable<number>;  // number | null
type MaybeString = Nullable<string>;  // string | null

// More complex type operators
type Readonly<T> = {
  readonly [P in keyof T]: T[P];
};

type Partial<T> = {
  [P in keyof T]?: T[P];
};
```

### Haskell Type Synonyms

```haskell
-- Type-level functions
type Pair a = (a, a)
type Endo a = a -> a

-- Higher-kinded type synonym
type Compose f g a = f (g a)

-- Example: Compose Maybe [] Int = Maybe [Int]
```

### Scala Type Aliases

```scala
// Type constructor aliases
type Pair[A] = (A, A)
type StringMap[V] = Map[String, V]

// Partially applied type constructors
type StringEither[A] = Either[String, A]
```

---

## Kind Errors in Real Languages

### Haskell Kind Errors

```haskell
-- This is a kind error:
-- Functor Int  -- Error! Int :: *, but Functor needs (* -> *)

-- Correct:
-- Functor Maybe  -- Maybe :: * -> *, OK!
-- Functor []     -- [] :: * -> *, OK!

-- GHC error message:
-- Expected kind '* -> *', but 'Int' has kind '*'
```

### Scala Kind Errors

```scala
// Kind error:
// def foo[F[_]](fa: F): Unit  -- Error! F needs a type argument

// Correct:
def foo[F[_], A](fa: F[A]): Unit
```

### TypeScript "Kind" Errors

```typescript
// TypeScript doesn't have explicit kinds, but...
type Apply<F, A> = F<A>;  // Error if F isn't generic!

// This works:
type Wrap<T> = { value: T };
type Applied = Wrap<number>;  // { value: number }

// This doesn't:
type NotGeneric = { value: number };
type Bad = NotGeneric<string>;  // Error! NotGeneric isn't generic
```

---

## Monad and Friends

### The Monad Type Class

```haskell
-- Monad requires (* -> *) kind
class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b

-- m :: * -> *
-- return :: ∀α. α → m α
-- (>>=)  :: ∀αβ. m α → (α → m β) → m β
```

### In Scala with Cats

```scala
import cats.Monad

// Monad[F] where F[_] has kind * -> *
implicit val optionMonad: Monad[Option] = new Monad[Option] {
  def pure[A](a: A): Option[A] = Some(a)
  def flatMap[A, B](fa: Option[A])(f: A => Option[B]): Option[B] =
    fa.flatMap(f)
  // ... tailRecM
}
```

### TypeScript with fp-ts

```typescript
import { Option, some, none, map, chain } from 'fp-ts/Option';

// Option is a type constructor: * -> *
const doubled: Option<number> = map((n: number) => n * 2)(some(5));

// chain is bind/flatMap
const result = chain((n: number) => n > 0 ? some(n) : none)(some(5));
```

---

## Real-World Applications

### 1. Effect Systems

```haskell
-- IO is a type constructor for effects
-- IO :: * -> *
main :: IO ()
main = do
  name <- getLine      -- getLine :: IO String
  putStrLn ("Hello " ++ name)  -- putStrLn :: String -> IO ()
```

### 2. Free Monads

```haskell
-- Free needs kind (* -> *) -> * -> *
data Free f a
  = Pure a
  | Free (f (Free f a))

-- f :: * -> *
-- Free :: (* -> *) -> * -> *
```

### 3. Monad Transformers

```haskell
-- Transformers stack monads
-- MaybeT :: (* -> *) -> * -> *
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

-- Stack IO with Maybe
type IOMaybe a = MaybeT IO a
```

### 4. Generic Programming

```haskell
-- Generic representation uses HKTs
class Generic a where
  type Rep a :: * -> *
  from :: a -> Rep a x
  to   :: Rep a x -> a
```

---

## The Functor-Applicative-Monad Hierarchy

```
       Functor
          │
          │  fmap :: (a -> b) -> f a -> f b
          ▼
     Applicative
          │
          │  pure  :: a -> f a
          │  (<*>) :: f (a -> b) -> f a -> f b
          ▼
        Monad
          │
          │  return :: a -> m a
          │  (>>=)  :: m a -> (a -> m b) -> m b
```

All require kind `(* -> *)`:
- `Functor f` where `f :: * -> *`
- `Applicative f` where `f :: * -> *`
- `Monad m` where `m :: * -> *`

---

## Simulating HKTs in Languages Without Them

### TypeScript Approach

```typescript
// Use interface + type mapping
interface HKT<URI, A> {
  readonly _URI: URI;
  readonly _A: A;
}

// Define "URI" for each type constructor
interface OptionHKT<A> extends HKT<'Option', A> {
  value: A | null;
}

// Functor interface
interface Functor<F> {
  map: <A, B>(fa: HKT<F, A>, f: (a: A) => B) => HKT<F, B>;
}
```

### Go Approach (Pre-Generics)

```go
// Before Go 1.18: use interface{} and type assertions
type Functor interface {
    Fmap(f func(interface{}) interface{}) Functor
}

// After Go 1.18: limited generics
type Functor[A any, F any] interface {
    Fmap(f func(A) any) F
}
// Still limited compared to true HKTs
```

---

## Key Takeaways for Practitioners

1. **Kinds classify type constructors**: `*`, `* -> *`, `(* -> *) -> *`

2. **Higher-kinded types enable abstraction**: Write code for any `Functor`, not just `List`

3. **Not all languages support HKTs**: Haskell, Scala yes; Go, Rust limited

4. **Type classes use kinds**: `Functor`, `Monad` work over `* -> *`

5. **Type-level programming**: Types as functions over types

---

## Tools and Libraries

- **Haskell**: Native HKT support, GHC
- **Scala**: cats, scalaz, shapeless
- **TypeScript**: fp-ts (simulated HKTs)
- **PureScript**: Native HKT support
- **Rust**: Generic Associated Types (GATs)
- **Kotlin**: Arrow library (simulated)
