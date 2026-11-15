-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/foveoos11_cm/tree_max_TreeMax_maxqtvc: the verification condition for
-- computing an integer maximum of a nonempty binary tree from maxima of its
-- right and left subtrees. This file contains no proof.

{-# OPTIONS --safe #-}

module tree_max_TreeMax_maxqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

Not : Set → Set
Not proposition = proposition → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

data Tree : Set where
  Null : Tree
  TreeNode : Int → Tree → Tree → Tree

mem : Int → Tree → Set
mem sought Null = ⊥
mem sought (TreeNode value leftTree rightTree) =
  value ≡ sought ∨ mem sought leftTree ∨ mem sought rightTree

geTree : Int → Tree → Set
geTree bound Null = ⊤
geTree bound (TreeNode value leftTree rightTree) =
  value ≤Z bound ∧
  geTree bound leftTree ∧
  geTree bound rightTree

BranchCondition : Tree → Set
BranchCondition Null = ⊥
BranchCondition (TreeNode value leftTree rightTree) = ⊤

ResultPremise : Tree → Int → Set
ResultPremise Null result = ⊥
ResultPremise (TreeNode value leftTree rightTree) result =
  Exists Int λ rightMaximum →
    (geTree rightMaximum rightTree ∧
     value ≤Z rightMaximum ∧
     (rightMaximum ≡ value ∨ mem rightMaximum rightTree)) ∧
    geTree result leftTree ∧
    rightMaximum ≤Z result ∧
    (result ≡ rightMaximum ∨ mem result leftTree)

ResultConclusion : Tree → Int → Set
ResultConclusion tree result =
  geTree result tree ∧ mem result tree

max'vc : Set
max'vc =
  (tree : Tree) →
  Not (tree ≡ Null) →
  BranchCondition tree ∧
  ((result : Int) →
    ResultPremise tree result →
    ResultConclusion tree result)
