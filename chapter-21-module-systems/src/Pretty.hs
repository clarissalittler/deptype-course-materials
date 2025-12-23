{-# LANGUAGE LambdaCase #-}

module Pretty
  ( prettyTerm
  , prettyType
  , prettyMod
  , prettySig
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.List (intercalate)

-- | Pretty print a type
prettyType :: Type -> String
prettyType = \case
  TyVar x -> x
  TyArr t1 t2 -> prettyTypeAtom t1 ++ " -> " ++ prettyType t2
  TyBool -> "Bool"
  TyNat -> "Nat"
  TyRecord fields ->
    "{" ++ intercalate ", " (map prettyField (Map.toList fields)) ++ "}"
    where
      prettyField (l, ty) = l ++ ": " ++ prettyType ty
  TyNamed t -> t

prettyTypeAtom :: Type -> String
prettyTypeAtom ty = case ty of
  TyArr {} -> "(" ++ prettyType ty ++ ")"
  _ -> prettyType ty

-- | Pretty print a term
prettyTerm :: Term -> String
prettyTerm = \case
  Var x -> x

  Lam x ty body ->
    "λ" ++ x ++ ":" ++ prettyType ty ++ ". " ++ prettyTerm body

  App t1 t2 -> prettyTermApp t1 ++ " " ++ prettyTermAtom t2

  TmTrue -> "true"
  TmFalse -> "false"

  TmIf t1 t2 t3 ->
    "if " ++ prettyTerm t1 ++ " then " ++ prettyTerm t2 ++ " else " ++ prettyTerm t3

  TmZero -> "0"
  TmSucc t -> case toNat t of
    Just n -> show (n + 1)
    Nothing -> "succ " ++ prettyTermAtom t

  TmPred t -> "pred " ++ prettyTermAtom t
  TmIsZero t -> "iszero " ++ prettyTermAtom t

  TmRecord fields ->
    "{" ++ intercalate ", " (map prettyField (Map.toList fields)) ++ "}"
    where
      prettyField (l, term) = l ++ " = " ++ prettyTerm term

  TmProj t label -> prettyTermAtom t ++ "." ++ label

  TmModProj (ModPath path var) _ ->
    intercalate "." (path ++ [var])

prettyTermAtom :: Term -> String
prettyTermAtom t = case t of
  Var {} -> prettyTerm t
  TmTrue -> prettyTerm t
  TmFalse -> prettyTerm t
  TmZero -> prettyTerm t
  TmSucc {} -> prettyTerm t
  TmRecord {} -> prettyTerm t
  TmModProj {} -> prettyTerm t
  _ -> "(" ++ prettyTerm t ++ ")"

prettyTermApp :: Term -> String
prettyTermApp t = case t of
  App {} -> prettyTerm t
  _ -> prettyTermAtom t

-- | Convert a term to a natural number if possible
toNat :: Term -> Maybe Integer
toNat TmZero = Just 0
toNat (TmSucc t) = (+ 1) <$> toNat t
toNat _ = Nothing

-- | Pretty print a module expression
prettyMod :: ModExpr -> String
prettyMod = \case
  Struct decls ->
    "struct\n" ++ unlines (map (("  " ++) . prettyDecl) decls) ++ "end"

  ModVar m -> m

  Functor x sig body ->
    "functor(" ++ x ++ " : " ++ prettySig sig ++ ") =>\n" ++ prettyMod body

  ModApp mf marg ->
    "(" ++ prettyMod mf ++ ")(" ++ prettyMod marg ++ ")"

  Seal m sig ->
    "(" ++ prettyMod m ++ " :> " ++ prettySig sig ++ ")"

prettyDecl :: Decl -> String
prettyDecl = \case
  ValDecl x ty t ->
    "val " ++ x ++ " : " ++ prettyType ty ++ " = " ++ prettyTerm t

  TypeDecl t mty -> case mty of
    Nothing -> "type " ++ t
    Just ty -> "type " ++ t ++ " = " ++ prettyType ty

  ModDecl m mexpr ->
    "module " ++ m ++ " = " ++ prettyMod mexpr

-- | Pretty print a signature
prettySig :: Signature -> String
prettySig (Sig specs) =
  "sig\n" ++ unlines (map (("  " ++) . prettySpec) specs) ++ "end"

prettySpec :: Spec -> String
prettySpec = \case
  ValSpec x ty ->
    "val " ++ x ++ " : " ++ prettyType ty

  TypeSpec t mty -> case mty of
    Nothing -> "type " ++ t
    Just ty -> "type " ++ t ++ " = " ++ prettyType ty

  ModSpec m sig ->
    "module " ++ m ++ " : " ++ prettySig sig
