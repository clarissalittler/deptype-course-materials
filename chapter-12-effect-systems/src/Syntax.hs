{-# LANGUAGE LambdaCase #-}

module Syntax
  ( -- * Variables
    Var
  , EffectLabel
    -- * Types
  , Type(..)
  , EffectRow(..)
    -- * Effects
  , Effect(..)
  , Operation(..)
    -- * Terms
  , Term(..)
  , Handler(..)
    -- * Free variables
  , freeVars
  , freeEffectVars
    -- * Substitution
  , substVar
  , freshVar
  ) where

import qualified Data.Set as Set
import Data.Set (Set)

-- | Variables are represented as strings
type Var = String

-- | Effect labels (e.g., "State", "Exception", "IO")
type EffectLabel = String

-- =============================================================================
-- Effects
-- =============================================================================

-- | An effect declaration
--
-- Effects are named and contain a set of operations.
-- Example: State s has operations get : () -> s and put : s -> ()
data Effect = Effect
  { effectName :: EffectLabel
  , effectOps  :: [Operation]
  }
  deriving (Eq, Show)

-- | An operation in an effect
--
-- Operations are the primitive actions that can be performed.
-- Example: get : () -> s  in State s
data Operation = Operation
  { opName   :: String      -- ^ Operation name (e.g., "get", "put")
  , opParam  :: Type        -- ^ Parameter type
  , opReturn :: Type        -- ^ Return type
  }
  deriving (Eq, Show, Ord)

-- =============================================================================
-- Effect Rows
-- =============================================================================

-- | Effect rows track which effects a computation may perform
--
-- Effect rows can be:
-- - Empty (pure computation)
-- - A set of concrete effects
-- - Open (polymorphic) with a row variable
--
-- Examples:
-- - {} - pure
-- - {State, Exception} - may use State or Exception
-- - {State | ρ} - State plus unknown effects ρ
data EffectRow
  = EffEmpty                      -- ^ No effects (pure)
  | EffLabel EffectLabel EffectRow -- ^ Effect label in row
  | EffVar Var                    -- ^ Effect row variable (for polymorphism)
  deriving (Eq, Show, Ord)

-- =============================================================================
-- Types
-- =============================================================================

-- | Types in the effect system
--
-- Key addition: Computation types A ! ε
-- where ε is the effect row
data Type
  = TyUnit                        -- ^ Unit type
  | TyBool                        -- ^ Boolean type
  | TyNat                         -- ^ Natural number type
  | TyFun Type Type EffectRow     -- ^ Function: A -> B ! ε
                                  -- ^ (function from A to B with effects ε)
  | TyForallEff Var Type          -- ^ Effect polymorphism: ∀ρ. A
  deriving (Eq, Show, Ord)

-- =============================================================================
-- Terms
-- =============================================================================

-- | Terms in the effect system
data Term
  = Var Var                       -- ^ Variable
  | Lam Var Type Term             -- ^ Lambda: λ(x: A). t
  | App Term Term                 -- ^ Application: t₁ t₂
  -- Booleans
  | TmTrue                        -- ^ true
  | TmFalse                       -- ^ false
  | TmIf Term Term Term           -- ^ if t₁ then t₂ else t₃
  -- Natural numbers
  | TmZero                        -- ^ 0
  | TmSucc Term                   -- ^ succ t
  | TmPred Term                   -- ^ pred t
  | TmIsZero Term                 -- ^ iszero t
  -- Unit
  | TmUnit                        -- ^ ()
  -- Let binding
  | TmLet Var Term Term           -- ^ let x = t₁ in t₂
  -- Effect operations
  | TmPerform EffectLabel String Term  -- ^ perform eff.op t
                                  -- ^ Perform an effect operation
  -- Effect handlers
  | TmHandle Term Handler         -- ^ handle t with h
                                  -- ^ Handle effects in t using handler h
  -- Effect abstraction/application
  | TmEffAbs Var Term             -- ^ Λρ. t (effect abstraction)
  | TmEffApp Term EffectRow       -- ^ t [ε] (effect application)
  -- Return (lift pure value into effectful computation)
  | TmReturn Term                 -- ^ return t
  deriving (Eq, Show)

-- =============================================================================
-- Handlers
-- =============================================================================

-- | Effect handler
--
-- A handler provides:
-- 1. A return clause: what to do with pure values
-- 2. Operation clauses: how to handle each operation
--
-- Example handler for State:
--   handler {
--     return x -> λs. (x, s)
--     get () k -> λs. k s s
--     put s' k -> λs. k () s'
--   }
data Handler = Handler
  { handlerEffect  :: EffectLabel       -- ^ Which effect this handles
  , handlerReturn  :: (Var, Term)       -- ^ return x -> body
  , handlerOps     :: [(String, Var, Var, Term)]
                                        -- ^ [(op, param, continuation, body)]
  }
  deriving (Eq, Show)

-- =============================================================================
-- Free Variables
-- =============================================================================

-- | Free variables in a term
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
  TmUnit -> Set.empty
  TmLet x t1 t2 -> freeVars t1 `Set.union` Set.delete x (freeVars t2)
  TmPerform _ _ t -> freeVars t
  TmHandle t h -> freeVars t `Set.union` handlerFreeVars h
  TmEffAbs _ t -> freeVars t
  TmEffApp t _ -> freeVars t
  TmReturn t -> freeVars t

-- | Free variables in a handler
handlerFreeVars :: Handler -> Set Var
handlerFreeVars h =
  let (retVar, retBody) = handlerReturn h
      retFvs = Set.delete retVar (freeVars retBody)
      opsFvs = Set.unions
        [ Set.delete p $ Set.delete k $ freeVars body
        | (_, p, k, body) <- handlerOps h
        ]
  in retFvs `Set.union` opsFvs

-- | Free effect row variables in a type
freeEffectVars :: Type -> Set Var
freeEffectVars = \case
  TyUnit -> Set.empty
  TyBool -> Set.empty
  TyNat -> Set.empty
  TyFun t1 t2 eff ->
    freeEffectVars t1 `Set.union` freeEffectVars t2 `Set.union` rowFreeVars eff
  TyForallEff v t -> Set.delete v (freeEffectVars t)

-- | Free variables in an effect row
rowFreeVars :: EffectRow -> Set Var
rowFreeVars = \case
  EffEmpty -> Set.empty
  EffLabel _ r -> rowFreeVars r
  EffVar v -> Set.singleton v

-- =============================================================================
-- Substitution
-- =============================================================================

-- | Substitute a term for a variable
substVar :: Var -> Term -> Term -> Term
substVar x s = \case
  Var y
    | y == x -> s
    | otherwise -> Var y
  Lam y ty t
    | y == x -> Lam y ty t
    | y `Set.member` fvs ->
        let y' = freshVar y (fvs `Set.union` freeVars t)
            t' = substVar y (Var y') t
        in Lam y' ty (substVar x s t')
    | otherwise -> Lam y ty (substVar x s t)
    where fvs = freeVars s
  App t1 t2 -> App (substVar x s t1) (substVar x s t2)
  TmTrue -> TmTrue
  TmFalse -> TmFalse
  TmIf t1 t2 t3 -> TmIf (substVar x s t1) (substVar x s t2) (substVar x s t3)
  TmZero -> TmZero
  TmSucc t -> TmSucc (substVar x s t)
  TmPred t -> TmPred (substVar x s t)
  TmIsZero t -> TmIsZero (substVar x s t)
  TmUnit -> TmUnit
  TmLet y t1 t2
    | y == x -> TmLet y (substVar x s t1) t2
    | y `Set.member` freeVars s ->
        let y' = freshVar y (freeVars s `Set.union` freeVars t2)
            t2' = substVar y (Var y') t2
        in TmLet y' (substVar x s t1) (substVar x s t2')
    | otherwise -> TmLet y (substVar x s t1) (substVar x s t2)
  TmPerform eff op t -> TmPerform eff op (substVar x s t)
  TmHandle t h -> TmHandle (substVar x s t) (substHandler x s h)
  TmEffAbs v t -> TmEffAbs v (substVar x s t)
  TmEffApp t eff -> TmEffApp (substVar x s t) eff
  TmReturn t -> TmReturn (substVar x s t)

-- | Substitute in a handler
substHandler :: Var -> Term -> Handler -> Handler
substHandler x s h = h
  { handlerReturn =
      let (v, body) = handlerReturn h
      in if v == x then (v, body) else (v, substVar x s body)
  , handlerOps =
      [ if p == x || k == x
        then (op, p, k, body)
        else (op, p, k, substVar x s body)
      | (op, p, k, body) <- handlerOps h
      ]
  }

-- | Generate a fresh variable
freshVar :: Var -> Set Var -> Var
freshVar base used = head $ filter (`Set.notMember` used) candidates
  where
    candidates = base : [base ++ show n | n <- [(1 :: Int) ..]]
