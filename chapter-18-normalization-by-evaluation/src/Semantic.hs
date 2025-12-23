{-# LANGUAGE LambdaCase #-}
-- | Semantic Domain for NbE
--
-- The semantic domain is where evaluation happens.
-- Values in this domain are:
--   - Closures (functions waiting for arguments)
--   - Neutral terms (stuck on a variable)
--   - Data (booleans, naturals, etc.)
--
-- The key insight: we use Haskell functions to represent lambda abstractions!
-- This is called "higher-order abstract syntax" (HOAS).

module Semantic
  ( -- * Semantic Values
    Val(..)
  , Closure(..)
    -- * Environments
  , Env
  , emptyEnv
  , extendEnv
  , lookupEnv
    -- * Neutral Values
  , Neutral(..)
  ) where

import Syntax (Name, Lvl, Term, Nf, Ne)

-- | Semantic values
--
-- These are the results of evaluation.
-- Notice: VLam contains a Haskell function!
data Val
  = VLam Name Closure        -- ^ Lambda closure
  | VPi Name Val Closure     -- ^ Pi type: domain and codomain closure
  | VU                       -- ^ Universe
  | VNe Neutral              -- ^ Neutral (stuck) value
  | VBool                    -- ^ Bool type
  | VTrue                    -- ^ true value
  | VFalse                   -- ^ false value
  | VNat                     -- ^ Nat type
  | VZero                    -- ^ zero value
  | VSuc Val                 -- ^ successor value

-- | A closure captures a term with its environment
--
-- We could use Haskell functions directly:
--   VLam (Val -> Val)
--
-- But explicit closures are better for:
--   - Debugging (can inspect the term)
--   - Serialization
--   - Some optimizations
data Closure = Closure Env Term
  deriving (Eq, Show)

-- Manual Eq and Show for Val (since we have closures)
instance Eq Val where
  VLam n1 c1 == VLam n2 c2 = n1 == n2 && c1 == c2
  VPi n1 a1 c1 == VPi n2 a2 c2 = n1 == n2 && a1 == a2 && c1 == c2
  VU == VU = True
  VNe n1 == VNe n2 = n1 == n2
  VBool == VBool = True
  VTrue == VTrue = True
  VFalse == VFalse = True
  VNat == VNat = True
  VZero == VZero = True
  VSuc v1 == VSuc v2 = v1 == v2
  _ == _ = False

instance Show Val where
  show (VLam n c) = "VLam " ++ show n ++ " " ++ show c
  show (VPi n a c) = "VPi " ++ show n ++ " " ++ show a ++ " " ++ show c
  show VU = "VU"
  show (VNe n) = "VNe " ++ show n
  show VBool = "VBool"
  show VTrue = "VTrue"
  show VFalse = "VFalse"
  show VNat = "VNat"
  show VZero = "VZero"
  show (VSuc v) = "VSuc (" ++ show v ++ ")"

-- | Neutral values
--
-- A neutral value is "stuck" on a free variable.
-- We track the spine of eliminations applied to it.
data Neutral
  = NVar Lvl                 -- ^ Free variable
  | NApp Neutral Val         -- ^ Application
  | NIf Neutral Val Val      -- ^ Conditional
  | NNatElim Val Val Val Neutral  -- ^ Natural number eliminator
  deriving (Eq, Show)

-- | Environment: maps de Bruijn indices to values
--
-- We use a list because indices count from the end.
type Env = [Val]

-- | Empty environment
emptyEnv :: Env
emptyEnv = []

-- | Extend environment with a new value
extendEnv :: Val -> Env -> Env
extendEnv v env = v : env

-- | Look up a value by de Bruijn index
lookupEnv :: Int -> Env -> Maybe Val
lookupEnv i env
  | i < length env = Just (env !! i)
  | otherwise = Nothing
