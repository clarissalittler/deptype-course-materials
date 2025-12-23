{-# LANGUAGE LambdaCase #-}
-- | Krivine Machine
--
-- The Krivine machine implements call-by-name (lazy) evaluation.
-- Unlike CEK which evaluates arguments before passing them,
-- Krivine delays argument evaluation until the argument is used.
--
-- The key difference:
--   CEK:     (\x. x + x) (1 + 2)  evaluates  1+2  once, then adds 3+3
--   Krivine: (\x. x + x) (1 + 2)  would evaluate  1+2  twice (without memoization)
--
-- State: (Term, Environment, Stack)
-- where the stack holds unevaluated closures (thunks).

module Krivine
  ( -- * Machine State
    State(..)
  , Thunk(..)
  , Stack
    -- * Evaluation
  , inject
  , step
  , eval
  , run
    -- * Tracing
  , trace
  ) where

import Syntax
import qualified Data.Map.Strict as Map

-- | A thunk: unevaluated term with its environment
data Thunk = Thunk Term KEnv
  deriving (Eq, Show)

-- | Krivine environment maps variables to thunks (not values!)
type KEnv = Map.Map Var Thunk

-- | Stack of thunks (arguments waiting to be consumed)
type Stack = [Thunk]

-- | Krivine machine state
data State = State
  { stTerm  :: Term
  , stEnv   :: KEnv
  , stStack :: Stack
  } deriving (Eq, Show)

-- | Empty environment
emptyKEnv :: KEnv
emptyKEnv = Map.empty

-- | Inject a term into initial state
inject :: Term -> State
inject t = State t emptyKEnv []

-- | Single step of Krivine machine
--
-- The rules are beautifully simple:
--
-- 1. Variable: Look up and continue with the thunk's term/env
-- 2. Lambda + non-empty stack: Bind parameter to top thunk, continue with body
-- 3. Application: Push argument as thunk, continue with function
--
step :: State -> Maybe State
step (State term env stack) = case term of
  -- Variable: substitute from environment
  TmVar x ->
    case Map.lookup x env of
      Just (Thunk t' e') -> Just $ State t' e' stack
      Nothing -> Nothing  -- Stuck: unbound variable

  -- Lambda with argument available: beta reduction
  TmLam x t | (thunk : stack') <- stack ->
    Just $ State t (Map.insert x thunk env) stack'

  -- Lambda with no arguments: we've reached weak head normal form
  TmLam _ _ ->
    Nothing  -- Normal form (not stuck, just done)

  -- Application: push argument as thunk
  TmApp t1 t2 ->
    Just $ State t1 env (Thunk t2 env : stack)

  -- Integer literal: need to force if there's a continuation
  TmInt _ ->
    Nothing  -- Normal form

  -- Arithmetic requires forcing both operands
  -- In pure Krivine, we'd need a more sophisticated approach
  -- This simplified version handles basic cases
  TmAdd t1 t2 ->
    -- For arithmetic, we need to actually evaluate
    case (evalToInt t1 env, evalToInt t2 env) of
      (Just n1, Just n2) -> Just $ State (TmInt (n1 + n2)) env stack
      _ -> Nothing

  TmSub t1 t2 ->
    case (evalToInt t1 env, evalToInt t2 env) of
      (Just n1, Just n2) -> Just $ State (TmInt (n1 - n2)) env stack
      _ -> Nothing

  TmMul t1 t2 ->
    case (evalToInt t1 env, evalToInt t2 env) of
      (Just n1, Just n2) -> Just $ State (TmInt (n1 * n2)) env stack
      _ -> Nothing

  -- If-zero: evaluate condition and branch
  TmIf0 t1 t2 t3 ->
    case evalToInt t1 env of
      Just 0 -> Just $ State t2 env stack
      Just _ -> Just $ State t3 env stack
      Nothing -> Nothing

  -- Let: desugar to application
  TmLet x t1 t2 ->
    Just $ State (TmApp (TmLam x t2) t1) env stack

  -- Fix: unfold once
  TmFix t ->
    Just $ State (TmApp t (TmFix t)) env stack

-- | Helper: evaluate a term to an integer (strict evaluation for arithmetic)
evalToInt :: Term -> KEnv -> Maybe Integer
evalToInt (TmInt n) _ = Just n
evalToInt (TmVar x) env =
  case Map.lookup x env of
    Just (Thunk t' e') -> evalToInt t' e'
    Nothing -> Nothing
evalToInt (TmAdd t1 t2) env =
  case (evalToInt t1 env, evalToInt t2 env) of
    (Just n1, Just n2) -> Just (n1 + n2)
    _ -> Nothing
evalToInt (TmSub t1 t2) env =
  case (evalToInt t1 env, evalToInt t2 env) of
    (Just n1, Just n2) -> Just (n1 - n2)
    _ -> Nothing
evalToInt (TmMul t1 t2) env =
  case (evalToInt t1 env, evalToInt t2 env) of
    (Just n1, Just n2) -> Just (n1 * n2)
    _ -> Nothing
evalToInt _ _ = Nothing

-- | Run machine to completion
eval :: State -> Maybe Value
eval state = case step state of
  Nothing ->
    -- Stopped: check if we have a value
    case stTerm state of
      TmInt n -> Just (VInt n)
      TmLam x t ->
        -- Convert thunk environment to value environment
        -- (This is a simplification)
        Just (VClosure x t emptyEnv)
      _ -> Nothing
  Just state' -> eval state'

-- | Convenience: run a term
run :: Term -> Maybe Value
run = eval . inject

-- | Trace execution
trace :: Term -> [State]
trace t = go (inject t)
  where
    go state = state : case step state of
      Nothing -> []
      Just state' -> go state'
