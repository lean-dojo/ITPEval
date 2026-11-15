-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_tree_reconstruction_TreeReconstruction_buildqtvc: the
-- verification condition for reconstructing a binary tree from its leaf-depth
-- list, covering successful suffix handling and reconstruction failure. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module vstte12_tree_reconstruction_TreeReconstruction_buildqtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 5 _++_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Tree : Set where
  Leaf : Tree
  Node : Tree → Tree → Tree

depths : Int → Tree → List Int
depths d Leaf = d ∷ []
depths d (Node left right) =
  depths (addInt d oneZ) left ++
  depths (addInt d oneZ) right

SuffixConclusion : List Int → Tree → List Int → Set
SuffixConclusion source tree [] =
  depths zeroZ tree ≡ source
SuffixConclusion source tree (_ ∷ _) =
  (other-tree : Tree) →
  Not (depths zeroZ other-tree ≡ source)

SuccessfulBuildCondition : List Int → Set
SuccessfulBuildCondition source =
  (tree : Tree) →
  (suffix : List Int) →
  source ≡ depths zeroZ tree ++ suffix →
  SuffixConclusion source tree suffix

NoDecomposition : List Int → Set
NoDecomposition source =
  (tree : Tree) →
  (suffix : List Int) →
  Not (depths zeroZ tree ++ suffix ≡ source)

FailureBuildCondition : List Int → Set
FailureBuildCondition source =
  NoDecomposition source →
  ((tree : Tree) → Not (depths zeroZ tree ≡ source))

build'vc : Set
build'vc =
  (source : List Int) →
  SuccessfulBuildCondition source ∧
  FailureBuildCondition source
