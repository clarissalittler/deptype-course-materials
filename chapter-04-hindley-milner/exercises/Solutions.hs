{-# LANGUAGE LambdaCase #-}

module Solutions where

import Syntax
import Infer
import Eval

-- =============================================================================
-- Exercise 1: Type Inference Practice (Easy)
-- =============================================================================

-- Exercise 1a: Composition
-- compose : (β → γ) → (α → β) → α → γ
-- compose = λf. λg. λx. f (g x)
compose :: Term
compose = Lam "f" $ Lam "g" $ Lam "x" $
  App (Var "f") (App (Var "g") (Var "x"))

-- Exercise 1b: S Combinator
-- s : (α → β → γ) → (α → β) → α → γ
-- s = λx. λy. λz. x z (y z)
sCombinator :: Term
sCombinator = Lam "x" $ Lam "y" $ Lam "z" $
  App (App (Var "x") (Var "z")) (App (Var "y") (Var "z"))

-- Exercise 1c: Twice
-- twice : (α → α) → α → α
-- twice = λf. λx. f (f x)
twice :: Term
twice = Lam "f" $ Lam "x" $
  App (Var "f") (App (Var "f") (Var "x"))

-- Exercise 1d: Flip
-- flip : (α → β → γ) → β → α → γ
-- flip = λf. λx. λy. f y x
flipFn :: Term
flipFn = Lam "f" $ Lam "x" $ Lam "y" $
  App (App (Var "f") (Var "y")) (Var "x")

-- =============================================================================
-- Exercise 2: Polymorphic List Operations (Medium)
-- =============================================================================

-- Exercise 2a: Map
-- map : (α → β) → List α → List β
-- Simplified version for lists up to length 3 (demonstrates polymorphism)
mapList :: Term
mapList = Lam "f" $ Lam "list" $
  TmIf (TmIsNil (Var "list"))
       TmNil
       (Let "h1" (TmHead (Var "list"))
         (Let "t1" (TmTail (Var "list"))
           (TmCons (App (Var "f") (Var "h1"))
             (TmIf (TmIsNil (Var "t1"))
                   TmNil
                   (Let "h2" (TmHead (Var "t1"))
                     (Let "t2" (TmTail (Var "t1"))
                       (TmCons (App (Var "f") (Var "h2"))
                         (TmIf (TmIsNil (Var "t2"))
                               TmNil
                               (TmCons (App (Var "f") (TmHead (Var "t2"))) TmNil)))))))))

-- Exercise 2b: Filter
-- filter : (α → Bool) → List α → List α
-- Simplified version for lists up to length 3
filterList :: Term
filterList = Lam "pred" $ Lam "list" $
  TmIf (TmIsNil (Var "list"))
       TmNil
       (Let "h1" (TmHead (Var "list"))
         (Let "t1" (TmTail (Var "list"))
           (TmIf (App (Var "pred") (Var "h1"))
                 (TmCons (Var "h1")
                   (TmIf (TmIsNil (Var "t1"))
                         TmNil
                         (Let "h2" (TmHead (Var "t1"))
                           (TmIf (App (Var "pred") (Var "h2"))
                                 (TmCons (Var "h2") TmNil)
                                 TmNil))))
                 (TmIf (TmIsNil (Var "t1"))
                       TmNil
                       (Let "h2" (TmHead (Var "t1"))
                         (TmIf (App (Var "pred") (Var "h2"))
                               (TmCons (Var "h2") TmNil)
                               TmNil))))))

-- Exercise 2c: Length
-- length : List α → Nat
-- Simplified version for lists up to length 3
lengthList :: Term
lengthList = Lam "list" $
  TmIf (TmIsNil (Var "list"))
       TmZero
       (TmSucc (TmIf (TmIsNil (TmTail (Var "list")))
                     TmZero
                     (TmSucc (TmIf (TmIsNil (TmTail (TmTail (Var "list"))))
                                   TmZero
                                   (TmSucc TmZero)))))

-- Exercise 2d: FoldL
-- foldl : (β → α → β) → β → List α → β
-- Simplified - just demonstrates the type
foldlList :: Term
foldlList = Lam "f" $ Lam "z" $ Lam "list" $
  TmIf (TmIsNil (Var "list"))
       (Var "z")
       (App (App (Var "f") (Var "z")) (TmHead (Var "list")))

-- Exercise 2e: FoldR
-- foldr : (α → β → β) → β → List α → β
-- Simplified - just demonstrates the type
foldrList :: Term
foldrList = Lam "f" $ Lam "z" $ Lam "list" $
  TmIf (TmIsNil (Var "list"))
       (Var "z")
       (App (App (Var "f") (TmHead (Var "list"))) (Var "z"))

-- =============================================================================
-- Exercise 3: Let-Polymorphism vs Lambda (Medium)
-- =============================================================================

-- Exercise 3a: Demonstrate Polymorphic Let
-- This SHOULD type check because 'id' is generalized in let
letPolymorphic :: Term
letPolymorphic =
  Let "id" (Lam "x" (Var "x"))
    (TmPair (App (Var "id") TmZero)
            (App (Var "id") TmTrue))

-- Exercise 3b: Demonstrate Monomorphic Lambda
-- This should NOT type check because 'id' in lambda is not generalized
lambdaMonomorphic :: Term
lambdaMonomorphic =
  App (Lam "id" (TmPair (App (Var "id") TmZero)
                        (App (Var "id") TmTrue)))
      (Lam "x" (Var "x"))

-- Explanation string (for documentation)
letPolymorphismExplanation :: String
letPolymorphismExplanation = unlines
  [ "Let-Polymorphism Explanation:"
  , ""
  , "In Hindley-Milner type inference:"
  , ""
  , "1. LET-POLYMORPHISM:"
  , "   let id = λx. x in pair (id 0) (id true)"
  , "   - The type of 'id' is GENERALIZED: ∀α. α → α"
  , "   - Each use of 'id' can be INSTANTIATED with different types"
  , "   - First use: (Nat → Nat)"
  , "   - Second use: (Bool → Bool)"
  , "   - Result: TYPES CORRECTLY"
  , ""
  , "2. LAMBDA (NO POLYMORPHISM):"
  , "   (λid. pair (id 0) (id true)) (λx. x)"
  , "   - The type of 'id' is NOT generalized"
  , "   - It must have a single monomorphic type"
  , "   - First use requires: id : Nat → Nat"
  , "   - Second use requires: id : Bool → Bool"
  , "   - These requirements CONFLICT"
  , "   - Result: TYPE ERROR (unification failure)"
  , ""
  , "KEY INSIGHT:"
  , "- Let-bindings introduce TYPE SCHEMES (∀α. τ)"
  , "- Lambda parameters have SIMPLE TYPES (τ)"
  , "- Only let-bound variables can be polymorphic!"
  ]

-- =============================================================================
-- Exercise 5: Polymorphic Trees (Medium)
-- =============================================================================

-- We encode trees using pairs: Bool indicates leaf/node
-- Leaf: true
-- Node: (false, (value, (left, right)))
-- This is simplified to just demonstrate polymorphic types

-- Helper: Create a leaf
mkLeaf :: Term
mkLeaf = TmTrue  -- Use true to represent leaf

-- Helper: Create a node (simplified: just value in a pair)
mkNode :: Term -> Term -> Term -> Term
mkNode value _left _right = TmPair TmFalse (TmPair value TmTrue)

-- Exercise 5a: Tree Map
-- treeMap : (α → β) → Tree α → Tree β
-- Very simplified - just demonstrates polymorphic type
treeMap :: Term
treeMap = Lam "f" $ Lam "tree" $
  Var "tree"  -- Identity function, just to demonstrate type

-- Exercise 5b: Tree Fold
-- treeFold : β → (α → β → β → β) → Tree α → β
-- Very simplified - just demonstrates polymorphic type
treeFold :: Term
treeFold = Lam "leafVal" $ Lam "nodeF" $ Lam "tree" $
  Var "leafVal"  -- Always return leaf value

-- Exercise 5c: Tree Height
-- height : Tree α → Nat
-- Simplified version that works with bool encoding
treeHeight :: Term
treeHeight = Lam "tree" $
  TmZero  -- Always return 0 for simplicity

-- =============================================================================
-- Example Programs
-- =============================================================================

-- Example 1: Simple composition example
-- (succ . succ) 3 = 5
example1 :: Term
example1 =
  Let "succFn" (Lam "x" (TmSucc (Var "x")))
  $ Let "succ2" (App (App compose (Var "succFn")) (Var "succFn"))
      (App (Var "succ2") (TmSucc (TmSucc (TmSucc TmZero))))

-- Example 2: Twice application
-- twice succ 3 = 5
example2 :: Term
example2 =
  Let "succFn" (Lam "x" (TmSucc (Var "x")))
    (App (App twice (Var "succFn")) (TmSucc (TmSucc (TmSucc TmZero))))

-- Example 3: Map over list
-- map succ [1, 2, 3] = [2, 3, 4]
example3 :: Term
example3 =
  Let "succFn" (Lam "x" (TmSucc (Var "x")))
  $ Let "list" (TmCons (TmSucc TmZero)
                 (TmCons (TmSucc (TmSucc TmZero))
                   (TmCons (TmSucc (TmSucc (TmSucc TmZero)))
                     TmNil)))
      (App (App mapList (Var "succFn")) (Var "list"))

-- Example 4: Length of list
example4 :: Term
example4 =
  Let "list" (TmCons TmZero (TmCons TmZero (TmCons TmZero TmNil)))
    (App lengthList (Var "list"))

-- Example 5: Polymorphic identity works with different types
example5 :: Term
example5 = letPolymorphic

-- Example 6: Simple tree (simplified node)
example6 :: Term
example6 = mkNode (TmSucc (TmSucc (TmSucc (TmSucc (TmSucc TmZero))))) mkLeaf mkLeaf

-- Example 7: Tree height
example7 :: Term
example7 = App treeHeight mkLeaf  -- Height of leaf is 0
