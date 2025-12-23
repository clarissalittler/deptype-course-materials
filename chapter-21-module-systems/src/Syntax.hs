{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables and Names
    Var
  , ModName
  , TypeName
  , Label
    -- * Types
  , Type(..)
    -- * Terms
  , Term(..)
    -- * Module Expressions
  , ModExpr(..)
    -- * Signatures
  , Signature(..)
  , Spec(..)
    -- * Module Paths
  , ModPath(..)
    -- * Free variables
  , freeVars
  , freeModVars
    -- * Substitution
  , substVar
  , freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- | Variables are represented as strings
type Var = String

-- | Module names
type ModName = String

-- | Type names
type TypeName = String

-- | Record field labels
type Label = String

-- | Types in the module system
--
-- We have a simple type system as the base for modules:
-- - TyNat, TyBool: Base types
-- - TyArr: Function types
-- - TyRecord: Record types
-- - TyNamed: Named types (type aliases defined in modules)
data Type
  = TyVar TypeName          -- ^ Type variable/name
  | TyArr Type Type         -- ^ Function type: τ₁ → τ₂
  | TyBool                  -- ^ Boolean type
  | TyNat                   -- ^ Natural number type
  | TyRecord (Map Label Type)  -- ^ Record type: {l₁: τ₁, l₂: τ₂, ...}
  | TyNamed TypeName        -- ^ Named type (from module)
  deriving (Eq, Show, Ord)

-- | Terms in the module system
--
-- These are the value-level expressions that can appear inside modules.
data Term
  = Var Var                     -- ^ Variable
  | Lam Var Type Term           -- ^ Lambda abstraction: λ(x:τ). t
  | App Term Term               -- ^ Application: t₁ t₂
  -- Booleans
  | TmTrue                      -- ^ Boolean literal: true
  | TmFalse                     -- ^ Boolean literal: false
  | TmIf Term Term Term         -- ^ Conditional: if t₁ then t₂ else t₃
  -- Natural numbers
  | TmZero                      -- ^ Natural number: 0
  | TmSucc Term                 -- ^ Successor: succ t
  | TmPred Term                 -- ^ Predecessor: pred t
  | TmIsZero Term               -- ^ Zero test: iszero t
  -- Records
  | TmRecord (Map Label Term)   -- ^ Record: {l₁ = t₁, l₂ = t₂, ...}
  | TmProj Term Label           -- ^ Projection: t.l
  -- Module access
  | TmModProj ModPath Var       -- ^ Module projection: M.N.x
  deriving (Eq, Show)

-- | Module paths for accessing nested module components
--
-- Examples:
-- - ModPath ["M"] "x"         -- M.x
-- - ModPath ["M", "N"] "x"    -- M.N.x
data ModPath
  = ModPath [ModName] Var     -- ^ Path through modules to a value
  deriving (Eq, Show)

-- | Module expressions
--
-- The core constructs for defining modules:
-- - Struct: A concrete module with definitions
-- - ModVar: Reference to a module by name
-- - Functor: Parameterized module (function from module to module)
-- - ModApp: Application of a functor to a module
-- - Seal: Restrict a module to a signature (M :> S)
data ModExpr
  = Struct [Decl]                    -- ^ Structure: struct { decls }
  | ModVar ModName                   -- ^ Module variable: M
  | Functor ModName Signature ModExpr  -- ^ Functor: functor(X : S) => M
  | ModApp ModExpr ModExpr           -- ^ Module application: F(M)
  | Seal ModExpr Signature           -- ^ Sealing/ascription: M :> S
  deriving (Eq, Show)

-- | Declarations inside a structure
data Decl
  = ValDecl Var Type Term            -- ^ Value declaration: val x : τ = t
  | TypeDecl TypeName (Maybe Type)   -- ^ Type declaration: type t [= τ]
  | ModDecl ModName ModExpr          -- ^ Module declaration: module M = ...
  deriving (Eq, Show)

-- | Signatures (module types)
--
-- A signature specifies what a module must provide:
-- - Value specifications: val x : τ
-- - Type specifications: type t (abstract) or type t = τ (manifest)
-- - Module specifications: module M : S
data Signature
  = Sig [Spec]                       -- ^ Signature: sig { specs }
  deriving (Eq, Show)

-- | Specifications in a signature
data Spec
  = ValSpec Var Type                 -- ^ Value spec: val x : τ
  | TypeSpec TypeName (Maybe Type)   -- ^ Type spec: type t [= τ]
  | ModSpec ModName Signature        -- ^ Module spec: module M : S
  deriving (Eq, Show)

-- | Compute the set of free variables in a term
freeVars :: Term -> Set Var
freeVars = \case
  Var x -> Set.singleton x
  Lam x _ t -> Set.delete x (freeVars t)
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  TmTrue -> Set.empty
  TmFalse -> Set.empty
  TmIf t1 t2 t3 -> freeVars t1 `Set.union` freeVars t2 `Set.union` freeVars t3
  TmZero -> Set.empty
  TmSucc t -> freeVars t
  TmPred t -> freeVars t
  TmIsZero t -> freeVars t
  TmRecord fields -> Set.unions (map freeVars (Map.elems fields))
  TmProj t _ -> freeVars t
  TmModProj _ _ -> Set.empty  -- Module paths are resolved separately

-- | Compute the set of free module variables
freeModVars :: ModExpr -> Set ModName
freeModVars = \case
  Struct decls -> Set.unions (map freeModVarsDecl decls)
  ModVar m -> Set.singleton m
  Functor x _ body -> Set.delete x (freeModVars body)
  ModApp m1 m2 -> freeModVars m1 `Set.union` freeModVars m2
  Seal m _ -> freeModVars m

freeModVarsDecl :: Decl -> Set ModName
freeModVarsDecl = \case
  ValDecl _ _ _ -> Set.empty
  TypeDecl _ _ -> Set.empty
  ModDecl _ m -> freeModVars m

-- | Capture-avoiding substitution: substVar x s t replaces x with s in t
-- [x ↦ s]t
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y
    | y == x -> s
    | otherwise -> Var y
  Lam y ty t
    | y == x -> Lam y ty t  -- x is shadowed
    | y `Set.member` fvs ->
        -- y is free in s, rename to avoid capture
        let y' = freshVar y (fvs `Set.union` freeVars t)
            t' = substVar y (Var y') t
        in Lam y' ty (substVar x s t')
    | otherwise -> Lam y ty (substVar x s t)
    where
      fvs = freeVars s
  App t1 t2 -> App (substVar x s t1) (substVar x s t2)
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 ->
    TmIf (substVar x s t1) (substVar x s t2) (substVar x s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substVar x s t)
  TmPred t -> TmPred (substVar x s t)
  TmIsZero t -> TmIsZero (substVar x s t)
  TmRecord fields -> TmRecord (Map.map (substVar x s) fields)
  TmProj t l -> TmProj (substVar x s t) l
  TmModProj p v -> TmModProj p v  -- Module projections unchanged

-- | Generate a fresh variable name
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
