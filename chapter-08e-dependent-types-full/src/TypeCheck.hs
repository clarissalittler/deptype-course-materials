{-# LANGUAGE LambdaCase #-}

module TypeCheck
  ( Context
  , TypeError(..)
  , typeOf
  , typeCheck
  , emptyCtx
  , extendCtx
  ) where

import Syntax
import NBE (normalize)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)

-- | Type context: maps variables to their types
type Context = Map Name Term

-- | Empty context
emptyCtx :: Context
emptyCtx = Map.empty

-- | Extend context with a new binding
extendCtx :: Name -> Term -> Context -> Context
extendCtx = Map.insert

-- | Type checking errors
data TypeError
  = UnboundVariable Name
  | TypeMismatch Term Term  -- expected, actual
  | NotAPi Term
  | NotASigma Term
  | NotAType Term
  | CannotInfer Term
  | NotSupported String
  | PatternError String
  deriving (Eq, Show)

-- | Definitional equality (NBE + alpha equivalence)
typeEq :: Term -> Term -> Bool
typeEq t1 t2 = alphaEq (normalize t1) (normalize t2)

-- | Cumulativity-aware convertibility
conv :: Term -> Term -> Bool
conv expected actual
  | typeEq expected actual = True
  | otherwise = case (normalize expected, normalize actual) of
      (Universe i, Universe j) -> j <= i
      _ -> False

-- | Infer the type of a term
typeOf :: Context -> Term -> Either TypeError Term
typeOf = infer

-- | Check that a term has a given type
typeCheck :: Context -> Term -> Term -> Either TypeError ()
typeCheck = check

infer :: Context -> Term -> Either TypeError Term
infer ctx = \case
  Universe i -> Right (Universe (i + 1))
  Var x -> case Map.lookup x ctx of
    Just ty -> Right ty
    Nothing -> Left (UnboundVariable x)
  Pi x a b -> do
    aType <- infer ctx a
    bType <- infer (extendCtx x a ctx) b
    case (normalize aType, normalize bType) of
      (Universe i, Universe j) -> Right (Universe (max i j))
      (Universe _, _) -> Left (NotAType b)
      _ -> Left (NotAType a)
  Sigma x a b -> do
    aType <- infer ctx a
    bType <- infer (extendCtx x a ctx) b
    case (normalize aType, normalize bType) of
      (Universe i, Universe j) -> Right (Universe (max i j))
      (Universe _, _) -> Left (NotAType b)
      _ -> Left (NotAType a)
  Lam x ty t -> do
    checkType ctx ty
    tyBody <- infer (extendCtx x ty ctx) t
    Right (Pi x ty tyBody)
  App t1 t2 -> do
    ty1 <- infer ctx t1
    case normalize ty1 of
      Pi x a b -> do
        check ctx t2 a
        Right (subst x t2 b)
      _ -> Left (NotAPi ty1)
  Pair t1 t2 -> Left (CannotInfer (Pair t1 t2))
  Fst t -> do
    ty <- infer ctx t
    case normalize ty of
      Sigma _ a _ -> Right a
      _ -> Left (NotASigma ty)
  Snd t -> do
    ty <- infer ctx t
    case normalize ty of
      Sigma x _ b -> Right (subst x (Fst t) b)
      _ -> Left (NotASigma ty)
  Nat -> Right (Universe 0)
  Zero -> Right Nat
  Succ t -> do
    check ctx t Nat
    Right Nat
  NatElim p z s n -> do
    pTy <- infer ctx p
    case normalize pTy of
      Pi _ a pBodyTy -> do
        if typeEq a Nat
          then case normalize pBodyTy of
            Universe _ -> do
              check ctx z (App p Zero)
              let stepTy =
                    Pi "k" Nat
                      (Pi "rec" (App p (Var "k"))
                        (App p (Succ (Var "k"))))
              check ctx s stepTy
              check ctx n Nat
              Right (App p n)
            _ -> Left (NotAType p)
          else Left (TypeMismatch Nat a)
      _ -> Left (NotAPi pTy)
  Bool -> Right (Universe 0)
  TmTrue -> Right Bool
  TmFalse -> Right Bool
  BoolElim p t f b -> do
    pTy <- infer ctx p
    case normalize pTy of
      Pi _ a pBodyTy -> do
        if typeEq a Bool
          then case normalize pBodyTy of
            Universe _ -> do
              check ctx t (App p TmTrue)
              check ctx f (App p TmFalse)
              check ctx b Bool
              Right (App p b)
            _ -> Left (NotAType p)
          else Left (TypeMismatch Bool a)
      _ -> Left (NotAPi pTy)
  Unit -> Right (Universe 0)
  TT -> Right Unit
  UnitElim p u x -> do
    pTy <- infer ctx p
    case normalize pTy of
      Pi _ a pBodyTy -> do
        if typeEq a Unit
          then case normalize pBodyTy of
            Universe _ -> do
              check ctx u (App p TT)
              check ctx x Unit
              Right (App p x)
            _ -> Left (NotAType p)
          else Left (TypeMismatch Unit a)
      _ -> Left (NotAPi pTy)
  Empty -> Right (Universe 0)
  EmptyElim p e -> do
    pTy <- infer ctx p
    case normalize pTy of
      Pi _ a pBodyTy -> do
        if typeEq a Empty
          then case normalize pBodyTy of
            Universe _ -> do
              check ctx e Empty
              Right (App p e)
            _ -> Left (NotAType p)
          else Left (TypeMismatch Empty a)
      _ -> Left (NotAPi pTy)
  Eq a x y -> do
    aTy <- infer ctx a
    case normalize aTy of
      Universe i -> do
        check ctx x a
        check ctx y a
        Right (Universe i)
      _ -> Left (NotAType a)
  Refl t -> do
    ty <- infer ctx t
    Right (Eq ty t t)
  J a c p x y eq -> do
    aTy <- infer ctx a
    case normalize aTy of
      Universe i -> do
        check ctx x a
        check ctx y a
        check ctx eq (Eq a x y)
        let cTy =
              Pi "z" a
                (Pi "e" (Eq a x (Var "z"))
                  (Universe i))
        check ctx c cTy
        check ctx p (App (App c x) (Refl x))
        Right (App (App c y) eq)
      _ -> Left (NotAType a)
  Ind name -> case name of
    "Vec" -> Right (Pi "A" (Universe 0) (Pi "n" Nat (Universe 0)))
    _ -> Left (NotSupported ("unknown inductive: " ++ name))
  Con name args -> inferConstructor ctx name args
  Match t motive branches -> inferMatch ctx t motive branches

check :: Context -> Term -> Term -> Either TypeError ()
check ctx term expected =
  case (term, normalize expected) of
    (Lam x ty body, Pi y a b) -> do
      checkType ctx ty
      if conv a ty
        then check (extendCtx x a ctx) body (subst y (Var x) b)
        else Left (TypeMismatch a ty)
    (Pair t1 t2, Sigma x a b) -> do
      check ctx t1 a
      check ctx t2 (subst x t1 b)
    _ -> do
      ty <- infer ctx term
      if conv expected ty
        then Right ()
        else Left (TypeMismatch expected ty)

checkType :: Context -> Term -> Either TypeError ()
checkType ctx t = do
  ty <- infer ctx t
  case normalize ty of
    Universe _ -> Right ()
    _ -> Left (NotAType t)

inferConstructor :: Context -> Name -> [Term] -> Either TypeError Term
inferConstructor ctx name args = case (name, args) of
  ("Nil", [ty]) -> do
    checkType ctx ty
    Right (App (App (Ind "Vec") ty) Zero)
  ("Cons", [ty, n, x, xs]) -> do
    checkType ctx ty
    check ctx n Nat
    check ctx x ty
    check ctx xs (App (App (Ind "Vec") ty) n)
    Right (App (App (Ind "Vec") ty) (Succ n))
  _ -> Left (NotSupported ("unknown constructor: " ++ name))

data MotiveKind
  = MotiveSimple
  | MotiveIndexed

inferMatch :: Context -> Term -> Maybe Term -> [(Pattern, Term)] -> Either TypeError Term
inferMatch ctx scrutinee motive branches = case motive of
  Nothing -> inferMatchNonDependent ctx scrutinee branches
  Just m -> inferMatchDependent ctx scrutinee m branches

inferMatchNonDependent :: Context -> Term -> [(Pattern, Term)] -> Either TypeError Term
inferMatchNonDependent ctx scrutinee branches = do
  scrutTy <- infer ctx scrutinee
  checkCoverage scrutTy (map fst branches)
  case branches of
    [] -> Left (PatternError "empty match")
    (pat, rhs):rest -> do
      (ctx1, patVars1) <- patternContext scrutTy pat
      ty1 <- infer (Map.union ctx1 ctx) rhs
      checkNonDependent patVars1 ty1
      mapM_ (checkBranch scrutTy ty1) rest
      Right ty1
  where
    checkBranch scrutTy expectedTy (pat, rhs) = do
      (ctxB, patVarsB) <- patternContext scrutTy pat
      tyB <- infer (Map.union ctxB ctx) rhs
      checkNonDependent patVarsB tyB
      if typeEq expectedTy tyB
        then Right ()
        else Left (TypeMismatch expectedTy tyB)

inferMatchDependent :: Context -> Term -> Term -> [(Pattern, Term)] -> Either TypeError Term
inferMatchDependent ctx scrutinee motive branches = do
  scrutTy <- infer ctx scrutinee
  checkCoverage scrutTy (map fst branches)
  let vecInfoM = vecInfoMaybe scrutTy
  motiveKind <- checkMotive ctx scrutTy vecInfoM motive
  let scrutIndex = case (motiveKind, vecInfoM) of
        (MotiveIndexed, Just (_, n)) -> n
        _ -> Zero
  case branches of
    [] -> Left (PatternError "empty match")
    _ -> do
      mapM_ (checkBranch motiveKind scrutTy) branches
      Right (applyMotive motiveKind scrutIndex scrutinee)
  where
    applyMotive kind idx tm = case kind of
      MotiveSimple -> App motive tm
      MotiveIndexed -> App (App motive idx) tm

    checkBranch kind scrutTy' (pat, rhs) = do
      (ctxB, patTerm, idxTerm) <- patternContextTerm ctx scrutTy' pat
      let expectedTy = applyMotive kind idxTerm patTerm
      check (Map.union ctxB ctx) rhs expectedTy

checkNonDependent :: Set Name -> Term -> Either TypeError ()
checkNonDependent patVars ty =
  if Set.null (freeVars ty `Set.intersection` patVars)
    then Right ()
    else Left (PatternError "branch type depends on pattern variables")

checkCoverage :: Term -> [Pattern] -> Either TypeError ()
checkCoverage scrutTy pats =
  case normalize scrutTy of
    App (App (Ind "Vec") _) n -> checkVecCoverage n pats
    _ -> Right ()

checkVecCoverage :: Term -> [Pattern] -> Either TypeError ()
checkVecCoverage n pats
  | null pats = Right ()
  | otherwise = do
      mapM_ (checkVecPatternPossible n) pats
      let (allowNil, allowCons) = vecAllowedConstructors n
      if any patternCoversAll pats
        then Right ()
        else do
          let hasNil = any patternIsNil pats
          let hasCons = any patternIsCons pats
          if allowNil && not hasNil
            then Left (PatternError "non-exhaustive patterns: missing Nil")
            else if allowCons && not hasCons
              then Left (PatternError "non-exhaustive patterns: missing Cons")
              else Right ()

checkVecPatternPossible :: Term -> Pattern -> Either TypeError ()
checkVecPatternPossible n pat =
  let (allowNil, allowCons) = vecAllowedConstructors n
  in case pat of
    PCon "Nil" _ | not allowNil ->
      Left (PatternError "impossible pattern: Nil does not match Vec (succ n)")
    PCon "Cons" _ | not allowCons ->
      Left (PatternError "impossible pattern: Cons does not match Vec 0")
    _ -> Right ()

vecAllowedConstructors :: Term -> (Bool, Bool)
vecAllowedConstructors n = case normalize n of
  Zero -> (True, False)
  Succ _ -> (False, True)
  _ -> (True, True)

patternCoversAll :: Pattern -> Bool
patternCoversAll = \case
  PVar _ -> True
  PWild -> True
  _ -> False

patternIsNil :: Pattern -> Bool
patternIsNil = \case
  PCon "Nil" _ -> True
  _ -> False

patternIsCons :: Pattern -> Bool
patternIsCons = \case
  PCon "Cons" _ -> True
  _ -> False

vecInfoMaybe :: Term -> Maybe (Term, Term)
vecInfoMaybe scrutTy = case normalize scrutTy of
  App (App (Ind "Vec") a) n -> Just (a, n)
  _ -> Nothing

checkMotive :: Context -> Term -> Maybe (Term, Term) -> Term -> Either TypeError MotiveKind
checkMotive ctx scrutTy vecInfoM motive = do
  motiveTy <- infer ctx motive
  case normalize motiveTy of
    Pi x a b
      | conv a scrutTy -> do
          checkType (extendCtx x a ctx) b
          Right MotiveSimple
    _ -> case vecInfoM of
      Just (scrutA, _) ->
        case normalize motiveTy of
          Pi n nTy body
            | conv nTy Nat -> case normalize body of
                Pi x vecTy b -> case normalize vecTy of
                  App (App (Ind "Vec") a') (Var nVar)
                    | nVar == n && conv a' scrutA -> do
                        checkType (extendCtx x vecTy (extendCtx n Nat ctx)) b
                        Right MotiveIndexed
                  _ -> Left (PatternError "motive must target Vec n")
                _ -> Left (PatternError "motive must be a function over Vec")
          _ -> Left (PatternError "motive must be a function over the scrutinee")
      Nothing -> Left (PatternError "motive must be a function over the scrutinee")

patternContextTerm :: Context -> Term -> Pattern -> Either TypeError (Context, Term, Term)
patternContextTerm ctx scrutTy pat =
  case normalize scrutTy of
    Nat -> patternForNatTerm ctx pat
    Bool -> patternForBoolTerm ctx pat
    Unit -> patternForUnitTerm ctx pat
    Empty -> patternForEmptyTerm ctx pat
    App (App (Ind "Vec") a) n -> patternForVecTerm ctx a n pat
    _ -> Left (PatternError "match scrutinee is not supported")

patternForNatTerm :: Context -> Pattern -> Either TypeError (Context, Term, Term)
patternForNatTerm ctx pat =
  let used0 = Map.keysSet ctx
  in case pat of
    PCon "Zero" [] -> Right (Map.empty, Zero, Zero)
    PCon "Succ" [p] -> do
      (ctxN, nTerm, _) <- bindTermTerm used0 Nat p
      let patTerm = Succ nTerm
      Right (ctxN, patTerm, patTerm)
    PVar x -> Right (Map.singleton x Nat, Var x, Var x)
    PWild -> do
      (ctxW, termW, _) <- bindTermTerm used0 Nat PWild
      Right (ctxW, termW, termW)
    _ -> Left (PatternError "unsupported pattern for Nat")

patternForBoolTerm :: Context -> Pattern -> Either TypeError (Context, Term, Term)
patternForBoolTerm ctx pat =
  let used0 = Map.keysSet ctx
  in case pat of
    PCon "True" [] -> Right (Map.empty, TmTrue, TmTrue)
    PCon "False" [] -> Right (Map.empty, TmFalse, TmFalse)
    PVar x -> Right (Map.singleton x Bool, Var x, Var x)
    PWild -> do
      (ctxW, termW, _) <- bindTermTerm used0 Bool PWild
      Right (ctxW, termW, termW)
    _ -> Left (PatternError "unsupported pattern for Bool")

patternForUnitTerm :: Context -> Pattern -> Either TypeError (Context, Term, Term)
patternForUnitTerm ctx pat =
  let used0 = Map.keysSet ctx
  in case pat of
    PCon "TT" [] -> Right (Map.empty, TT, TT)
    PVar x -> Right (Map.singleton x Unit, Var x, Var x)
    PWild -> do
      (ctxW, termW, _) <- bindTermTerm used0 Unit PWild
      Right (ctxW, termW, termW)
    _ -> Left (PatternError "unsupported pattern for Unit")

patternForEmptyTerm :: Context -> Pattern -> Either TypeError (Context, Term, Term)
patternForEmptyTerm ctx pat =
  let used0 = Map.keysSet ctx
  in case pat of
    PVar x -> Right (Map.singleton x Empty, Var x, Var x)
    PWild -> do
      (ctxW, termW, _) <- bindTermTerm used0 Empty PWild
      Right (ctxW, termW, termW)
    _ -> Left (PatternError "unsupported pattern for Empty")

patternForVecTerm :: Context -> Term -> Term -> Pattern -> Either TypeError (Context, Term, Term)
patternForVecTerm ctx a n pat = case pat of
  PWild -> do
    let vecTy = App (App (Ind "Vec") a) n
    (ctxW, termW, _) <- bindTermTerm (Map.keysSet ctx) vecTy PWild
    Right (ctxW, termW, n)
  PVar x -> do
    let vecTy = App (App (Ind "Vec") a) n
    Right (Map.singleton x vecTy, Var x, n)
  PCon "Nil" [pA] -> do
    (ctxA, aTerm, _) <- bindTypeParamTerm (Map.keysSet ctx) a pA
    let patTerm = Con "Nil" [aTerm]
    Right (ctxA, patTerm, Zero)
  PCon "Cons" [pA, pN, pX, pXS] -> do
    let used0 = Map.keysSet ctx
    (ctxA, aTerm, used1) <- bindTypeParamTerm used0 a pA
    (ctxN, nTerm, used2) <- bindIndexTerm used1 pN
    (ctxX, xTerm, used3) <- bindTermTerm used2 aTerm pX
    let xsTy = App (App (Ind "Vec") aTerm) nTerm
    (ctxXS, xsTerm, _) <- bindTermTerm used3 xsTy pXS
    let patTerm = Con "Cons" [aTerm, nTerm, xTerm, xsTerm]
    let ctxAll = Map.unions [ctxA, ctxN, ctxX, ctxXS]
    Right (ctxAll, patTerm, Succ nTerm)
  _ -> Left (PatternError "unsupported pattern for Vec")

bindTypeParamTerm :: Set Name -> Term -> Pattern -> Either TypeError (Context, Term, Set Name)
bindTypeParamTerm used a = \case
  PWild -> Right (Map.empty, a, used)
  PVar x -> Right (Map.singleton x (Universe 0), Var x, Set.insert x used)
  _ -> Left (PatternError "type parameter must be variable or _")

bindIndexTerm :: Set Name -> Pattern -> Either TypeError (Context, Term, Set Name)
bindIndexTerm used = \case
  PVar x -> Right (Map.singleton x Nat, Var x, Set.insert x used)
  PWild ->
    let (x, used') = freshInternal used
    in Right (Map.singleton x Nat, Var x, used')
  _ -> Left (PatternError "index must be variable or _")

bindTermTerm :: Set Name -> Term -> Pattern -> Either TypeError (Context, Term, Set Name)
bindTermTerm used ty = \case
  PVar x -> Right (Map.singleton x ty, Var x, Set.insert x used)
  PWild ->
    let (x, used') = freshInternal used
    in Right (Map.singleton x ty, Var x, used')
  _ -> Left (PatternError "pattern must be variable or _")

freshInternal :: Set Name -> (Name, Set Name)
freshInternal used =
  let name = freshName "_wild" used
  in (name, Set.insert name used)

patternContext :: Term -> Pattern -> Either TypeError (Context, Set Name)
patternContext scrutTy pat =
  case normalize scrutTy of
    Nat -> patternForNat pat
    Bool -> patternForBool pat
    Unit -> patternForUnit pat
    Empty -> patternForEmpty pat
    App (App (Ind "Vec") a) n -> patternForVec a n pat
    _ -> Left (PatternError "match scrutinee is not supported")

patternForVec :: Term -> Term -> Pattern -> Either TypeError (Context, Set Name)
patternForVec a n pat = case pat of
  PWild -> Right (Map.empty, Set.empty)
  PVar x -> do
    let vecTy = App (App (Ind "Vec") a) n
    Right (Map.singleton x vecTy, Set.singleton x)
  PCon "Nil" [pA] -> do
    (ctxA, varsA) <- bindTypeParam a pA
    Right (ctxA, varsA)
  PCon "Cons" [pA, pN, pX, pXS] -> do
    (ctxA, varsA) <- bindTypeParam a pA
    (ctxN, varsN, nTerm) <- bindIndex pN
    let aVar = case pA of
          PVar x -> Var x
          _ -> a
    (ctxX, varsX) <- bindTerm aVar pX
    let xsTy = App (App (Ind "Vec") aVar) nTerm
    (ctxXS, varsXS) <- bindTerm xsTy pXS
    let ctxAll = Map.unions [ctxA, ctxN, ctxX, ctxXS]
    let varsAll = Set.unions [varsA, varsN, varsX, varsXS]
    Right (ctxAll, varsAll)
  _ -> Left (PatternError "unsupported pattern for Vec")

patternForNat :: Pattern -> Either TypeError (Context, Set Name)
patternForNat pat = case pat of
  PCon "Zero" [] -> Right (Map.empty, Set.empty)
  PCon "Succ" [p] -> bindTerm Nat p
  PVar x -> Right (Map.singleton x Nat, Set.singleton x)
  PWild -> Right (Map.empty, Set.empty)
  _ -> Left (PatternError "unsupported pattern for Nat")

patternForBool :: Pattern -> Either TypeError (Context, Set Name)
patternForBool pat = case pat of
  PCon "True" [] -> Right (Map.empty, Set.empty)
  PCon "False" [] -> Right (Map.empty, Set.empty)
  PVar x -> Right (Map.singleton x Bool, Set.singleton x)
  PWild -> Right (Map.empty, Set.empty)
  _ -> Left (PatternError "unsupported pattern for Bool")

patternForUnit :: Pattern -> Either TypeError (Context, Set Name)
patternForUnit pat = case pat of
  PCon "TT" [] -> Right (Map.empty, Set.empty)
  PVar x -> Right (Map.singleton x Unit, Set.singleton x)
  PWild -> Right (Map.empty, Set.empty)
  _ -> Left (PatternError "unsupported pattern for Unit")

patternForEmpty :: Pattern -> Either TypeError (Context, Set Name)
patternForEmpty pat = case pat of
  PVar x -> Right (Map.singleton x Empty, Set.singleton x)
  PWild -> Right (Map.empty, Set.empty)
  _ -> Left (PatternError "unsupported pattern for Empty")

bindTypeParam :: Term -> Pattern -> Either TypeError (Context, Set Name)
bindTypeParam _ PWild = Right (Map.empty, Set.empty)
bindTypeParam _ (PVar x) = Right (Map.singleton x (Universe 0), Set.singleton x)
bindTypeParam _ _ = Left (PatternError "type parameter must be variable or _")

bindTerm :: Term -> Pattern -> Either TypeError (Context, Set Name)
bindTerm _ PWild = Right (Map.empty, Set.empty)
bindTerm ty (PVar x) = Right (Map.singleton x ty, Set.singleton x)
bindTerm _ _ = Left (PatternError "pattern must be variable or _")

bindIndex :: Pattern -> Either TypeError (Context, Set Name, Term)
bindIndex (PVar x) = Right (Map.singleton x Nat, Set.singleton x, Var x)
bindIndex _ = Left (PatternError "index must be a variable")
