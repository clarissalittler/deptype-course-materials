{-# LANGUAGE LambdaCase #-}

module Pretty
  ( -- * Pretty printing
    prettyTerm
  , prettyType
    -- * Rendering
  , render
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.List (intercalate)

-- =============================================================================
-- Pretty Printing Types
-- =============================================================================

-- | Pretty print a type
prettyType :: Type -> String
prettyType = go False
  where
    go _ = \case
      TyVar v -> v
      TyBool -> "Bool"
      TyNat -> "Nat"
      TyTop -> "Top"
      TyBot -> "Bot"
      TyRecord fields ->
        "{" ++ intercalate ", " [l ++ ": " ++ go False t | (l, t) <- Map.toList fields] ++ "}"
      TyArr t1 t2 ->
        -- Arrow is right-associative, so only parenthesize left side if needed
        let left = case t1 of
              TyArr {} -> "(" ++ go False t1 ++ ")"
              _ -> go False t1
            right = go False t2
        in left ++ " -> " ++ right

-- =============================================================================
-- Pretty Printing Terms
-- =============================================================================

-- | Pretty print a term
prettyTerm :: Term -> String
prettyTerm = go 0
  where
    -- Precedence levels:
    -- 0: top level (lambda, if, ascription)
    -- 1: application
    -- 2: projection
    -- 3: atoms
    go :: Int -> Term -> String
    go _ = \case
      Var x -> x

      Lam x ty t ->
        "λ" ++ x ++ ":" ++ prettyType ty ++ ". " ++ go 0 t

      App t1 t2 ->
        go 1 t1 ++ " " ++ goArg t2

      TmTrue -> "true"
      TmFalse -> "false"

      TmIf t1 t2 t3 ->
        "if " ++ go 0 t1 ++ " then " ++ go 0 t2 ++ " else " ++ go 0 t3

      TmZero -> "0"

      TmSucc t ->
        -- Print natural numbers nicely
        case toNat (TmSucc t) of
          Just n -> show n
          Nothing -> "succ " ++ goArg t

      TmPred t -> "pred " ++ goArg t

      TmIsZero t -> "iszero " ++ goArg t

      TmRecord fields ->
        "{" ++ intercalate ", " [l ++ " = " ++ go 0 t | (l, t) <- Map.toList fields] ++ "}"

      TmProj t label ->
        goArg t ++ "." ++ label

      TmAscribe t ty ->
        ascribeLHS t ++ " as " ++ prettyType ty

    -- Argument position: wrap complex terms in parens
    goArg :: Term -> String
    goArg t@(Var _) = go 0 t
    goArg t@TmTrue = go 0 t
    goArg t@TmFalse = go 0 t
    goArg t@TmZero = go 0 t
    goArg t@(TmSucc _) = case toNat t of
      Just n -> show n
      Nothing -> "(" ++ go 0 t ++ ")"
    goArg t@(TmRecord _) = go 0 t
    goArg t@(TmProj _ _) = go 0 t
    goArg t = "(" ++ go 0 t ++ ")"

    ascribeLHS :: Term -> String
    ascribeLHS t = case t of
      Lam {} -> "(" ++ go 0 t ++ ")"
      TmIf {} -> "(" ++ go 0 t ++ ")"
      TmAscribe {} -> "(" ++ go 0 t ++ ")"
      _ -> go 1 t

-- | Try to convert a term to a natural number
toNat :: Term -> Maybe Int
toNat TmZero = Just 0
toNat (TmSucc t) = (+ 1) <$> toNat t
toNat _ = Nothing

-- | Render for display (identity for now)
render :: String -> String
render = id
