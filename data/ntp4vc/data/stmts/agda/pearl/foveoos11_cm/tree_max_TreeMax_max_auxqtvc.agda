-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/foveoos11_cm/tree_max_TreeMax_max_auxqtvc: the auxiliary verification
-- condition for computing an integer maximum over a binary tree with an
-- accumulator. This file contains no proof.

{-# OPTIONS --safe #-}

module tree_max_TreeMax_max_auxqtvc where

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

maxInt : Int → Int → Int
maxInt x y with intLess x y
... | true = y
... | false = x

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

ChildMatch : Tree → Tree → Set
ChildMatch Null child = ⊥
ChildMatch (TreeNode value firstChild secondChild) child =
  firstChild ≡ child ∨ secondChild ≡ child

FirstConjunct : Tree → Int → Set
FirstConjunct Null accumulator = ⊤
FirstConjunct
  whole@(TreeNode value leftTree rightTree)
  accumulator =
    let accumulatorMaximum = maxInt value accumulator
    in
    ChildMatch whole rightTree ∧
    ((rightMaximum : Int) →
      (geTree rightMaximum rightTree ∧
       accumulatorMaximum ≤Z rightMaximum ∧
       (rightMaximum ≡ accumulatorMaximum ∨
        mem rightMaximum rightTree)) →
      ChildMatch whole leftTree)

ResultPremise : Tree → Int → Int → Set
ResultPremise Null accumulator result =
  result ≡ accumulator
ResultPremise
  (TreeNode value leftTree rightTree)
  accumulator
  result =
    let accumulatorMaximum = maxInt value accumulator
    in
    Exists Int λ rightMaximum →
      (geTree rightMaximum rightTree ∧
       accumulatorMaximum ≤Z rightMaximum ∧
       (rightMaximum ≡ accumulatorMaximum ∨
        mem rightMaximum rightTree)) ∧
      geTree result leftTree ∧
      rightMaximum ≤Z result ∧
      (result ≡ rightMaximum ∨ mem result leftTree)

ResultConclusion : Tree → Int → Int → Set
ResultConclusion tree accumulator result =
  geTree result tree ∧
  accumulator ≤Z result ∧
  (result ≡ accumulator ∨ mem result tree)

max-aux'vc : Set
max-aux'vc =
  (tree : Tree) →
  (accumulator : Int) →
  FirstConjunct tree accumulator ∧
  ((result : Int) →
    ResultPremise tree accumulator result →
    ResultConclusion tree accumulator result)
