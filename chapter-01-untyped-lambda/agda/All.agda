------------------------------------------------------------------------
-- Untyped Lambda Calculus - Agda Formalization
--
-- This module re-exports all modules for the untyped lambda calculus
-- formalization.
--
-- To type-check all modules:
--   agda All.agda
--
-- Modules:
--   Syntax      - Term definition using de Bruijn indices
--   Evaluation  - Small-step operational semantics
--   Properties  - Determinism, divergence of Ω
------------------------------------------------------------------------

module All where

open import Syntax public
open import Evaluation public
open import Properties public
