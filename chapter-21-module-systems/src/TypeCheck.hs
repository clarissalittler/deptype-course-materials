{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( -- * Type checking
    typeOf
  , typeCheck
  , typeCheckMod
    -- * Signature matching
  , matchSignature
  , (<:)
    -- * Contexts
  , TypeContext
  , ModuleContext
  , emptyContext
  , lookupVar
  , lookupMod
  , extendVar
  , extendMod
  ) where

import Syntax
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Monad (foldM)

-- | Type context for value-level variables
type TypeContext = Map Var Type

-- | Module context
-- Maps module names to their signatures
type ModuleContext = (TypeContext, Map ModName Signature, Map TypeName Type)

-- | Empty context
emptyContext :: ModuleContext
emptyContext = (Map.empty, Map.empty, Map.empty)

-- | Look up a variable in the context
lookupVar :: Var -> ModuleContext -> Maybe Type
lookupVar x (ctx, _, _) = Map.lookup x ctx

-- | Look up a module in the context
lookupMod :: ModName -> ModuleContext -> Maybe Signature
lookupMod m (_, mctx, _) = Map.lookup m mctx

-- | Look up a type name
lookupType :: TypeName -> ModuleContext -> Maybe Type
lookupType t (_, _, tctx) = Map.lookup t tctx

-- | Extend context with a variable
extendVar :: Var -> Type -> ModuleContext -> ModuleContext
extendVar x ty (ctx, mctx, tctx) = (Map.insert x ty ctx, mctx, tctx)

-- | Extend context with a module
extendMod :: ModName -> Signature -> ModuleContext -> ModuleContext
extendMod m sig (ctx, mctx, tctx) = (ctx, Map.insert m sig mctx, tctx)

-- | Extend context with a type
extendType :: TypeName -> Type -> ModuleContext -> ModuleContext
extendType t ty (ctx, mctx, tctx) = (ctx, mctx, Map.insert t ty tctx)

-- | Type checking with explicit context
typeOf :: ModuleContext -> Term -> Either String Type
typeOf ctx = \case
  Var x ->
    case lookupVar x ctx of
      Nothing -> Left $ "Unbound variable: " ++ x
      Just ty -> Right ty

  Lam x ty body ->
    let ctx' = extendVar x ty ctx
    in TyArr ty <$> typeOf ctx' body

  App t1 t2 -> do
    ty1 <- typeOf ctx t1
    ty2 <- typeOf ctx t2
    case ty1 of
      TyArr tyArg tyRes ->
        if tyArg == ty2
        then Right tyRes
        else Left $ "Type mismatch in application: expected " ++ show tyArg ++ ", got " ++ show ty2
      _ -> Left $ "Expected function type, got " ++ show ty1

  TmTrue -> Right TyBool
  TmFalse -> Right TyBool

  TmIf t1 t2 t3 -> do
    ty1 <- typeOf ctx t1
    case ty1 of
      TyBool -> do
        ty2 <- typeOf ctx t2
        ty3 <- typeOf ctx t3
        if ty2 == ty3
        then Right ty2
        else Left $ "Branches have different types: " ++ show ty2 ++ " vs " ++ show ty3
      _ -> Left "Condition must be Bool"

  TmZero -> Right TyNat

  TmSucc t -> do
    ty <- typeOf ctx t
    case ty of
      TyNat -> Right TyNat
      _ -> Left $ "succ expects Nat, got " ++ show ty

  TmPred t -> do
    ty <- typeOf ctx t
    case ty of
      TyNat -> Right TyNat
      _ -> Left $ "pred expects Nat, got " ++ show ty

  TmIsZero t -> do
    ty <- typeOf ctx t
    case ty of
      TyNat -> Right TyBool
      _ -> Left $ "iszero expects Nat, got " ++ show ty

  TmRecord fields -> do
    fieldTys <- traverse (typeOf ctx) fields
    Right $ TyRecord fieldTys

  TmProj t label -> do
    ty <- typeOf ctx t
    case ty of
      TyRecord fields ->
        case Map.lookup label fields of
          Nothing -> Left $ "Record does not have field: " ++ label
          Just fieldTy -> Right fieldTy
      _ -> Left $ "Projection requires record type, got " ++ show ty

  TmModProj (ModPath path x) _ -> do
    -- Resolve the module path and get the type of x
    sig <- resolveModPath ctx path
    case lookupValSpec x sig of
      Nothing -> Left $ "Module does not have value: " ++ x
      Just ty -> Right ty

-- | Resolve a module path to a signature
resolveModPath :: ModuleContext -> [ModName] -> Either String Signature
resolveModPath ctx [] = Left "Empty module path"
resolveModPath ctx [m] =
  case lookupMod m ctx of
    Nothing -> Left $ "Unbound module: " ++ m
    Just sig -> Right sig
resolveModPath ctx (m:ms) = do
  sig <- case lookupMod m ctx of
    Nothing -> Left $ "Unbound module: " ++ m
    Just s -> Right s
  case lookupModSpec (head ms) sig of
    Nothing -> Left $ "Module " ++ m ++ " does not have submodule: " ++ head ms
    Just subsig -> resolveModPath ctx ms

-- | Look up a value specification in a signature
lookupValSpec :: Var -> Signature -> Maybe Type
lookupValSpec x (Sig specs) = go specs
  where
    go [] = Nothing
    go (ValSpec y ty : rest)
      | x == y = Just ty
      | otherwise = go rest
    go (_ : rest) = go rest

-- | Look up a module specification in a signature
lookupModSpec :: ModName -> Signature -> Maybe Signature
lookupModSpec m (Sig specs) = go specs
  where
    go [] = Nothing
    go (ModSpec n sig : rest)
      | m == n = Just sig
      | otherwise = go rest
    go (_ : rest) = go rest

-- | Type check a term (no context)
typeCheck :: Term -> Either String Type
typeCheck = typeOf emptyContext

-- | Type check a module expression
typeCheckMod :: ModuleContext -> ModExpr -> Either String Signature
typeCheckMod ctx = \case
  Struct decls -> do
    -- Check all declarations and build a signature
    (sig, _) <- foldM checkDecl (Sig [], ctx) decls
    Right sig

  ModVar m ->
    case lookupMod m ctx of
      Nothing -> Left $ "Unbound module: " ++ m
      Just sig -> Right sig

  Functor x sig body -> do
    -- Type check the body with the parameter in context
    let ctx' = extendMod x sig ctx
    bodySig <- typeCheckMod ctx' body
    -- A functor's signature is a function from sig to bodySig
    -- For simplicity, we represent it as the body signature
    Right bodySig

  ModApp mf marg -> do
    -- Type check the functor
    sigf <- typeCheckMod ctx mf
    -- Type check the argument
    sigarg <- typeCheckMod ctx marg

    -- For functor application, we need to extract the parameter signature
    -- and result signature from the functor, then check that sigarg matches
    -- the parameter signature
    -- For simplicity, we just return the functor's signature
    -- (A full implementation would track functor types properly)
    Right sigf

  Seal m sig -> do
    -- Check that the module matches the signature
    sigm <- typeCheckMod ctx m
    case matchSignature sigm sig of
      Right () -> Right sig
      Left err -> Left err

-- | Check a declaration and update the signature and context
checkDecl :: (Signature, ModuleContext) -> Decl -> Either String (Signature, ModuleContext)
checkDecl (Sig specs, ctx) decl = case decl of
  ValDecl x ty t -> do
    -- Type check the term
    ty' <- typeOf ctx t
    if ty == ty'
    then let spec = ValSpec x ty
             ctx' = extendVar x ty ctx
         in Right (Sig (specs ++ [spec]), ctx')
    else Left $ "Type mismatch in value declaration: expected " ++ show ty ++ ", got " ++ show ty'

  TypeDecl t mty -> do
    let spec = TypeSpec t mty
        ctx' = case mty of
          Just ty -> extendType t ty ctx
          Nothing -> ctx  -- Abstract type
    Right (Sig (specs ++ [spec]), ctx')

  ModDecl m mexpr -> do
    sig <- typeCheckMod ctx mexpr
    let spec = ModSpec m sig
        ctx' = extendMod m sig ctx
    Right (Sig (specs ++ [spec]), ctx')

-- | Check if one signature matches (is a subtype of) another
-- sig1 <: sig2 means sig1 provides at least what sig2 requires
matchSignature :: Signature -> Signature -> Either String ()
matchSignature (Sig impl) (Sig req) = mapM_ checkSpec req
  where
    checkSpec :: Spec -> Either String ()
    checkSpec spec = case spec of
      ValSpec x ty ->
        case findValSpec x impl of
          Nothing -> Left $ "Missing value: " ++ x
          Just ty' ->
            if ty == ty'
            then Right ()
            else Left $ "Type mismatch for " ++ x ++ ": expected " ++ show ty ++ ", got " ++ show ty'

      TypeSpec t mty ->
        case findTypeSpec t impl of
          Nothing -> Left $ "Missing type: " ++ t
          Just mty' -> case (mty, mty') of
            -- Abstract type in requirement can be satisfied by any type
            (Nothing, _) -> Right ()
            -- Manifest type must match exactly
            (Just ty, Just ty') ->
              if ty == ty'
              then Right ()
              else Left $ "Type mismatch for " ++ t
            (Just _, Nothing) ->
              Left $ "Expected manifest type for " ++ t ++ ", got abstract"

      ModSpec m sig ->
        case findModSpec m impl of
          Nothing -> Left $ "Missing module: " ++ m
          Just sig' -> matchSignature sig' sig

    findValSpec :: Var -> [Spec] -> Maybe Type
    findValSpec x = go
      where
        go [] = Nothing
        go (ValSpec y ty : _) | x == y = Just ty
        go (_ : rest) = go rest

    findTypeSpec :: TypeName -> [Spec] -> Maybe (Maybe Type)
    findTypeSpec t = go
      where
        go [] = Nothing
        go (TypeSpec t' mty : _) | t == t' = Just mty
        go (_ : rest) = go rest

    findModSpec :: ModName -> [Spec] -> Maybe Signature
    findModSpec m = go
      where
        go [] = Nothing
        go (ModSpec m' sig : _) | m == m' = Just sig
        go (_ : rest) = go rest

-- | Signature subtyping operator
(<:) :: Signature -> Signature -> Bool
sig1 <: sig2 = case matchSignature sig1 sig2 of
  Right () -> True
  Left _ -> False
