{-# LANGUAGE LambdaCase #-}

module Syntax
  ( Name, Level
  , Term(..), Pattern(..)
  , InductiveDef(..), Constructor(..)
  , freeVars
  , patternVars
  , subst
  , freshName
  , alphaEq
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)

type Name = String
type Level = Int

-- | Inductive type definition
data InductiveDef = InductiveDef
  { indName :: Name           -- Name of the type
  , indParams :: [(Name, Term)]  -- Parameters (e.g., A in Vec A n)
  , indIndices :: [(Name, Term)] -- Indices (e.g., n in Vec A n)
  , indType :: Term           -- Type of the inductive type
  , indConstructors :: [Constructor]
  } deriving (Eq, Show)

-- | Constructor of an inductive type
data Constructor = Constructor
  { conName :: Name
  , conType :: Term           -- Type of the constructor
  } deriving (Eq, Show)

-- | Patterns for pattern matching
data Pattern
  = PVar Name                 -- Variable pattern
  | PCon Name [Pattern]       -- Constructor pattern
  | PWild                     -- Wildcard _
  deriving (Eq, Show, Ord)

-- | Terms in full dependent type theory
data Term
  -- Universe hierarchy
  = Universe Level            -- Type i (where i is the level)

  -- Variables and binding
  | Var Name
  | Lam Name Term Term        -- λ(x:A). t
  | App Term Term             -- t₁ t₂

  -- Dependent types
  | Pi Name Term Term         -- Π(x:A). B
  | Sigma Name Term Term      -- Σ(x:A). B
  | Pair Term Term            -- (t₁, t₂)
  | Fst Term                  -- fst t
  | Snd Term                  -- snd t

  -- Inductive types
  | Ind Name                  -- Reference to inductive type
  | Con Name [Term]           -- Constructor application
  | Match Term (Maybe Term) [(Pattern, Term)] -- Pattern matching (optional motive)

  -- Equality type (propositional equality)
  | Eq Term Term Term         -- Eq A x y  (x = y in type A)
  | Refl Term                 -- refl x    (proof that x = x)
  | J Term Term Term Term Term Term
    -- J(A, C, p, x, y, eq)
    -- Elimination principle for equality
    -- If eq : x = y, C : (z:A) → x = z → Type, p : C x (refl x)
    -- then J produces C y eq

  -- Natural numbers (built-in for convenience)
  | Nat
  | Zero
  | Succ Term
  | NatElim Term Term Term Term
    -- natElim(P, z, s, n)
    -- P : Nat → Type, z : P 0, s : Π(k:Nat). P k → P (succ k), n : Nat

  -- Booleans
  | Bool
  | TmTrue
  | TmFalse
  | BoolElim Term Term Term Term
    -- boolElim(P, t, f, b)
    -- P : Bool → Type, t : P true, f : P false, b : Bool

  -- Unit and Empty types
  | Unit
  | TT                        -- () : Unit
  | UnitElim Term Term Term
    -- unitElim(P, u, x)
    -- P : Unit → Type, u : P (), x : Unit

  | Empty                     -- ⊥ (empty type, no constructors)
  | EmptyElim Term Term
    -- emptyElim(P, e)
    -- P : Empty → Type, e : Empty
    -- Can eliminate to any type (ex falso quodlibet)

  deriving (Eq, Show, Ord)

-- | Free variables in a term
freeVars :: Term -> Set Name
freeVars = \case
  Universe _ -> Set.empty
  Var x -> Set.singleton x
  Lam x ty t -> Set.delete x (freeVars ty `Set.union` freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Pi x a b -> Set.delete x (freeVars a `Set.union` freeVars b)
  Sigma x a b -> Set.delete x (freeVars a `Set.union` freeVars b)
  Pair t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Fst t -> freeVars t
  Snd t -> freeVars t
  Ind _ -> Set.empty
  Con _ ts -> Set.unions (map freeVars ts)
  Match t motive branches ->
    freeVars t `Set.union`
    maybe Set.empty freeVars motive `Set.union`
    Set.unions [freeVars rhs Set.\\ patternVars pat | (pat, rhs) <- branches]
  Eq a x y -> freeVars a `Set.union` freeVars x `Set.union` freeVars y
  Refl t -> freeVars t
  J a c p x y eq -> Set.unions [freeVars a, freeVars c, freeVars p, freeVars x, freeVars y, freeVars eq]
  Nat -> Set.empty
  Zero -> Set.empty
  Succ t -> freeVars t
  NatElim p z s n -> Set.unions [freeVars p, freeVars z, freeVars s, freeVars n]
  Bool -> Set.empty
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  BoolElim p t f b -> Set.unions [freeVars p, freeVars t, freeVars f, freeVars b]
  Unit -> Set.empty
  TT -> Set.empty
  UnitElim p u x -> Set.unions [freeVars p, freeVars u, freeVars x]
  Empty -> Set.empty
  EmptyElim p e -> freeVars p `Set.union` freeVars e

-- | Variables in a pattern
patternVars :: Pattern -> Set Name
patternVars = \case
  PVar x -> Set.singleton x
  PCon _ ps -> Set.unions (map patternVars ps)
  PWild -> Set.empty

-- | Substitution: [x ↦ s]t
subst :: Name -> Term -> Term -> Term
subst x s = \case
  Universe l -> Universe l
  Var y | y == x -> s
        | otherwise -> Var y
  Lam y ty t
    | y == x -> Lam y (subst x s ty) t
    | y `Set.member` fvs ->
        let y' = freshName y (fvs `Set.union` freeVars t `Set.union` freeVars ty)
            t' = subst y (Var y') t
            ty' = subst y (Var y') ty
        in Lam y' (subst x s ty') (subst x s t')
    | otherwise -> Lam y (subst x s ty) (subst x s t)
    where fvs = freeVars s
  App t1 t2 -> App (subst x s t1) (subst x s t2)
  Pi y a b
    | y == x -> Pi y (subst x s a) b
    | y `Set.member` fvs ->
        let y' = freshName y (fvs `Set.union` freeVars a `Set.union` freeVars b)
            a' = subst y (Var y') a
            b' = subst y (Var y') b
        in Pi y' (subst x s a') (subst x s b')
    | otherwise -> Pi y (subst x s a) (subst x s b)
    where fvs = freeVars s
  Sigma y a b
    | y == x -> Sigma y (subst x s a) b
    | y `Set.member` fvs ->
        let y' = freshName y (fvs `Set.union` freeVars a `Set.union` freeVars b)
            a' = subst y (Var y') a
            b' = subst y (Var y') b
        in Sigma y' (subst x s a') (subst x s b')
    | otherwise -> Sigma y (subst x s a) (subst x s b)
    where fvs = freeVars s
  Pair t1 t2 -> Pair (subst x s t1) (subst x s t2)
  Fst t -> Fst (subst x s t)
  Snd t -> Snd (subst x s t)
  Ind name -> Ind name
  Con name ts -> Con name (map (subst x s) ts)
  Match t motive branches -> Match (subst x s t) (fmap (subst x s) motive) (map substBranch branches)
    where
      substBranch (pat, rhs)
        | x `Set.member` patternVars pat = (pat, rhs)
        | otherwise =
            let avoid = freeVars s
                patVars = patternVars pat
            in if Set.null (Set.intersection patVars avoid)
              then (pat, subst x s rhs)
              else
                let (pat', renames) = freshenPattern pat (avoid `Set.union` freeVars rhs)
                    rhs' = applyRenames renames rhs
                in (pat', subst x s rhs')

      freshenPattern :: Pattern -> Set Name -> (Pattern, Map Name Name)
      freshenPattern pat used =
        let (pat', mapping, _) = go pat used Map.empty
            renames = Map.filterWithKey (\k v -> k /= v) mapping
        in (pat', renames)

      go :: Pattern -> Set Name -> Map Name Name -> (Pattern, Map Name Name, Set Name)
      go PWild used mapping = (PWild, mapping, used)
      go (PVar y) used mapping =
        case Map.lookup y mapping of
          Just y' -> (PVar y', mapping, used)
          Nothing ->
            if y `Set.member` used
              then
                let y' = freshName y used
                    mapping' = Map.insert y y' mapping
                    used' = Set.insert y' used
                in (PVar y', mapping', used')
              else
                let mapping' = Map.insert y y mapping
                    used' = Set.insert y used
                in (PVar y, mapping', used')
      go (PCon name ps) used mapping =
        let (ps', mapping', used') =
              foldl step ([], mapping, used) ps
            step (acc, m, u) p =
              let (p', m', u') = go p u m
              in (acc ++ [p'], m', u')
        in (PCon name ps', mapping', used')

      applyRenames :: Map Name Name -> Term -> Term
      applyRenames renames rhs =
        foldr (\(old, new) acc -> subst old (Var new) acc) rhs (Map.toList renames)
  Eq a t1 t2 -> Eq (subst x s a) (subst x s t1) (subst x s t2)
  Refl t -> Refl (subst x s t)
  J a c p x1 y eq -> J (subst x s a) (subst x s c) (subst x s p) (subst x s x1) (subst x s y) (subst x s eq)
  Nat -> Nat
  Zero -> Zero
  Succ t -> Succ (subst x s t)
  NatElim p z step n -> NatElim (subst x s p) (subst x s z) (subst x s step) (subst x s n)
  Bool -> Bool
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  BoolElim p t f b -> BoolElim (subst x s p) (subst x s t) (subst x s f) (subst x s b)
  Unit -> Unit
  TT -> TT
  UnitElim p u val -> UnitElim (subst x s p) (subst x s u) (subst x s val)
  Empty -> Empty
  EmptyElim p e -> EmptyElim (subst x s p) (subst x s e)

-- | Generate a fresh name
freshName :: Name -> Set Name -> Name
freshName base used = head $ filter (`Set.notMember` used) candidates
  where candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]

-- | Alpha equivalence (structural equality up to variable renaming)
alphaEq :: Term -> Term -> Bool
alphaEq = go Set.empty Set.empty
  where
    go :: Set (Name, Name) -> Set (Name, Name) -> Term -> Term -> Bool
    go bound1 bound2 t1 t2 = case (t1, t2) of
      (Universe l1, Universe l2) -> l1 == l2
      (Var x, Var y) -> x == y || Set.member (x, y) bound1 || Set.member (y, x) bound2
      (Lam x ty1 t1', Lam y ty2 t2') ->
        go bound1 bound2 ty1 ty2 &&
        go (Set.insert (x, y) bound1) (Set.insert (y, x) bound2) t1' t2'
      (App a1 a2, App b1 b2) -> go bound1 bound2 a1 b1 && go bound1 bound2 a2 b2
      (Pi x a1 b1, Pi y a2 b2) ->
        go bound1 bound2 a1 a2 &&
        go (Set.insert (x, y) bound1) (Set.insert (y, x) bound2) b1 b2
      (Sigma x a1 b1, Sigma y a2 b2) ->
        go bound1 bound2 a1 a2 &&
        go (Set.insert (x, y) bound1) (Set.insert (y, x) bound2) b1 b2
      (Pair a1 a2, Pair b1 b2) -> go bound1 bound2 a1 b1 && go bound1 bound2 a2 b2
      (Fst a, Fst b) -> go bound1 bound2 a b
      (Snd a, Snd b) -> go bound1 bound2 a b
      (Ind n1, Ind n2) -> n1 == n2
      (Con n1 ts1, Con n2 ts2) -> n1 == n2 && length ts1 == length ts2 &&
        all (uncurry (go bound1 bound2)) (zip ts1 ts2)
      (Match t1' m1 bs1, Match t2' m2 bs2) ->
        go bound1 bound2 t1' t2' &&
        motiveEq bound1 bound2 m1 m2 &&
        length bs1 == length bs2 &&
        and (zipWith (branchEq bound1 bound2) bs1 bs2)
      (Eq a1 x1 y1, Eq a2 x2 y2) ->
        go bound1 bound2 a1 a2 && go bound1 bound2 x1 x2 && go bound1 bound2 y1 y2
      (Refl a, Refl b) -> go bound1 bound2 a b
      (J a1 c1 p1 x1 y1 eq1, J a2 c2 p2 x2 y2 eq2) ->
        go bound1 bound2 a1 a2 &&
        go bound1 bound2 c1 c2 &&
        go bound1 bound2 p1 p2 &&
        go bound1 bound2 x1 x2 &&
        go bound1 bound2 y1 y2 &&
        go bound1 bound2 eq1 eq2
      (Nat, Nat) -> True
      (Zero, Zero) -> True
      (Succ a, Succ b) -> go bound1 bound2 a b
      (NatElim p1 z1 s1 n1, NatElim p2 z2 s2 n2) ->
        go bound1 bound2 p1 p2 &&
        go bound1 bound2 z1 z2 &&
        go bound1 bound2 s1 s2 &&
        go bound1 bound2 n1 n2
      (Bool, Bool) -> True
      (TmTrue, TmTrue) -> True
      (TmFalse, TmFalse) -> True
      (BoolElim p1 t1' f1 b1, BoolElim p2 t2' f2 b2) ->
        go bound1 bound2 p1 p2 &&
        go bound1 bound2 t1' t2' &&
        go bound1 bound2 f1 f2 &&
        go bound1 bound2 b1 b2
      (Unit, Unit) -> True
      (TT, TT) -> True
      (UnitElim p1 u1 x1, UnitElim p2 u2 x2) ->
        go bound1 bound2 p1 p2 &&
        go bound1 bound2 u1 u2 &&
        go bound1 bound2 x1 x2
      (Empty, Empty) -> True
      (EmptyElim p1 e1, EmptyElim p2 e2) ->
        go bound1 bound2 p1 p2 &&
        go bound1 bound2 e1 e2
      _ -> False

    branchEq :: Set (Name, Name) -> Set (Name, Name)
             -> (Pattern, Term) -> (Pattern, Term) -> Bool
    branchEq b1 b2 (pat1, rhs1) (pat2, rhs2) =
      case extendFromPattern pat1 pat2 b1 b2 of
        Just (b1', b2') -> go b1' b2' rhs1 rhs2
        Nothing -> False

    motiveEq :: Set (Name, Name) -> Set (Name, Name)
             -> Maybe Term -> Maybe Term -> Bool
    motiveEq b1 b2 m1 m2 = case (m1, m2) of
      (Nothing, Nothing) -> True
      (Just t1, Just t2) -> go b1 b2 t1 t2
      _ -> False

    extendFromPattern :: Pattern -> Pattern -> Set (Name, Name) -> Set (Name, Name)
                      -> Maybe (Set (Name, Name), Set (Name, Name))
    extendFromPattern p1 p2 b1 b2 = case (p1, p2) of
      (PWild, PWild) -> Just (b1, b2)
      (PVar x, PVar y) -> addPair b1 b2 x y
      (PCon c1 ps1, PCon c2 ps2)
        | c1 == c2 && length ps1 == length ps2 ->
            foldl step (Just (b1, b2)) (zip ps1 ps2)
        | otherwise -> Nothing
      _ -> Nothing
      where
        step acc (pa, pb) = acc >>= \(b1', b2') -> extendFromPattern pa pb b1' b2'

    addPair :: Set (Name, Name) -> Set (Name, Name) -> Name -> Name
            -> Maybe (Set (Name, Name), Set (Name, Name))
    addPair b1 b2 x y =
      case lookupBound b1 x of
        Just y' -> if y' == y then Just (b1, b2) else Nothing
        Nothing ->
          case lookupBound b2 y of
            Just x' -> if x' == x then Just (b1, b2) else Nothing
            Nothing -> Just (Set.insert (x, y) b1, Set.insert (y, x) b2)

    lookupBound :: Set (Name, Name) -> Name -> Maybe Name
    lookupBound b x = case [y | (x', y) <- Set.toList b, x' == x] of
      (y:_) -> Just y
      [] -> Nothing
