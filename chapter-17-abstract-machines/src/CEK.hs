{-# LANGUAGE LambdaCase #-}
-- | CEK Machine
--
-- The CEK machine is a classic abstract machine for call-by-value evaluation.
-- CEK stands for:
--   C - Control (the current term being evaluated)
--   E - Environment (bindings for free variables)
--   K - Kontinuation (what to do after evaluating the current term)
--
-- The key insight is that the continuation makes the evaluation context explicit,
-- turning the recursive substitution-based semantics into an iterative machine.

module CEK
  ( -- * Machine State
    State(..)
  , Kont(..)
  , Frame(..)
    -- * Evaluation
  , inject
  , step
  , eval
  , run
    -- * Tracing
  , trace
  ) where

import Syntax

-- | CEK machine state
data State
  = Eval Term Env Kont      -- ^ Evaluating a term
  | Apply Kont Value        -- ^ Applying a continuation to a value
  deriving (Eq, Show)

-- | Continuation (evaluation context as a list of frames)
--
-- This is the reified "rest of the computation".
-- We use a list of frames instead of nested data for efficiency.
type Kont = [Frame]

-- | A single frame in the continuation
--
-- Each frame represents one level of the evaluation context.
data Frame
  = FApp1 Term Env          -- ^ [_ t2] - evaluating function, arg waiting
  | FApp2 Value             -- ^ [v1 _] - function done, evaluating argument
  | FAdd1 Term Env          -- ^ [_ + t2]
  | FAdd2 Value             -- ^ [v1 + _]
  | FSub1 Term Env          -- ^ [_ - t2]
  | FSub2 Value             -- ^ [v1 - _]
  | FMul1 Term Env          -- ^ [_ * t2]
  | FMul2 Value             -- ^ [v1 * _]
  | FIf0 Term Term Env      -- ^ [if0 _ then t2 else t3]
  | FLet Var Term Env       -- ^ [let x = _ in t2]
  | FFix Env                -- ^ [fix _]
  deriving (Eq, Show)

-- | Inject a term into the initial machine state
inject :: Term -> State
inject t = Eval t emptyEnv []

-- | Take one step of the machine
--
-- Returns Nothing if the machine is stuck or finished.
step :: State -> Maybe State
step state = case state of
  -- Evaluating a variable: look it up in the environment
  Eval (TmVar x) env k ->
    case lookupEnv x env of
      Just v  -> Just $ Apply k v
      Nothing -> Nothing  -- Stuck: unbound variable

  -- Evaluating a lambda: create a closure
  Eval (TmLam x t) env k ->
    Just $ Apply k (VClosure x t env)

  -- Evaluating an application: evaluate the function first
  Eval (TmApp t1 t2) env k ->
    Just $ Eval t1 env (FApp1 t2 env : k)

  -- Evaluating an integer: it's already a value
  Eval (TmInt n) _env k ->
    Just $ Apply k (VInt n)

  -- Evaluating addition: evaluate first operand
  Eval (TmAdd t1 t2) env k ->
    Just $ Eval t1 env (FAdd1 t2 env : k)

  -- Evaluating subtraction
  Eval (TmSub t1 t2) env k ->
    Just $ Eval t1 env (FSub1 t2 env : k)

  -- Evaluating multiplication
  Eval (TmMul t1 t2) env k ->
    Just $ Eval t1 env (FMul1 t2 env : k)

  -- Evaluating if0
  Eval (TmIf0 t1 t2 t3) env k ->
    Just $ Eval t1 env (FIf0 t2 t3 env : k)

  -- Evaluating let
  Eval (TmLet x t1 t2) env k ->
    Just $ Eval t1 env (FLet x t2 env : k)

  -- Evaluating fix
  Eval (TmFix t) env k ->
    Just $ Eval t env (FFix env : k)

  -- Applying a continuation: process the next frame
  Apply [] v ->
    Nothing  -- Done! (final state, not stuck)

  -- Application: function evaluated, now evaluate argument
  Apply (FApp1 t2 env : k) v1 ->
    Just $ Eval t2 env (FApp2 v1 : k)

  -- Application: both done, apply the function
  Apply (FApp2 (VClosure x t env) : k) v2 ->
    Just $ Eval t (extendEnv x v2 env) k

  Apply (FApp2 (VInt _) : _) _ ->
    Nothing  -- Stuck: applying an integer

  -- Addition: first operand done
  Apply (FAdd1 t2 env : k) v1 ->
    Just $ Eval t2 env (FAdd2 v1 : k)

  -- Addition: both done
  Apply (FAdd2 (VInt n1) : k) (VInt n2) ->
    Just $ Apply k (VInt (n1 + n2))

  Apply (FAdd2 _ : _) _ ->
    Nothing  -- Stuck: adding non-integers

  -- Subtraction
  Apply (FSub1 t2 env : k) v1 ->
    Just $ Eval t2 env (FSub2 v1 : k)

  Apply (FSub2 (VInt n1) : k) (VInt n2) ->
    Just $ Apply k (VInt (n1 - n2))

  Apply (FSub2 _ : _) _ ->
    Nothing

  -- Multiplication
  Apply (FMul1 t2 env : k) v1 ->
    Just $ Eval t2 env (FMul2 v1 : k)

  Apply (FMul2 (VInt n1) : k) (VInt n2) ->
    Just $ Apply k (VInt (n1 * n2))

  Apply (FMul2 _ : _) _ ->
    Nothing

  -- If0: condition evaluated
  Apply (FIf0 t2 t3 env : k) (VInt n) ->
    if n == 0
      then Just $ Eval t2 env k
      else Just $ Eval t3 env k

  Apply (FIf0 _ _ _ : _) (VClosure _ _ _) ->
    Nothing  -- Stuck: if0 on closure

  -- Let: binding evaluated
  Apply (FLet x t2 env : k) v ->
    Just $ Eval t2 (extendEnv x v env) k

  -- Fix: argument evaluated (should be a closure)
  Apply (FFix _ : k) (VClosure f body fenv) ->
    -- fix (\f. body) = body[f := fix (\f. body)]
    -- For call-by-value, body should be a lambda \n. inner
    -- The fixed point is VClosure "n" inner {f: fixVal}
    -- where fixVal is this same closure (the fixed point itself)
    case body of
      TmLam n inner ->
        -- Use Haskell's laziness to create the cyclic structure
        let fixVal = VClosure n inner (extendEnv f fixVal fenv)
        in Just $ Apply k fixVal
      _ ->
        -- If body is not a lambda, evaluate it in the recursive environment
        let fixV = VClosure f body (extendEnv f fixV fenv)
        in Just $ Eval body (extendEnv f fixV fenv) k

  Apply (FFix _ : _) (VInt _) ->
    Nothing  -- Stuck: fix on integer

-- | Run the machine until it halts
eval :: State -> Maybe Value
eval state = case step state of
  Nothing ->
    -- Machine halted
    case state of
      Apply [] v -> Just v   -- Normal termination
      _          -> Nothing  -- Stuck
  Just state' ->
    eval state'

-- | Convenience function: evaluate a term
run :: Term -> Maybe Value
run = eval . inject

-- | Trace execution: return list of all states
trace :: Term -> [State]
trace t = go (inject t)
  where
    go state = state : case step state of
      Nothing -> []
      Just state' -> go state'
