------------------------------------------------------------------------
-- Simply Typed Lambda Calculus - Agda Formalization
--
-- This module re-exports all modules for the STLC formalization.
--
-- To type-check all modules:
--   agda All.agda
--
-- Modules:
--   Syntax       - Types, contexts, intrinsically-typed terms
--   Evaluation   - Small-step semantics, values, multi-step reduction
--   Progress     - Progress theorem (well-typed terms don't get stuck)
--   Preservation - Preservation theorem (reduction preserves types)
--
-- Key Results:
--   - Type Safety = Progress + Preservation
--   - Determinism of evaluation
--   - Intrinsic typing makes preservation "free"
------------------------------------------------------------------------

module All where

open import Syntax public
open import Evaluation public
open import Progress public
open import Preservation public
