-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_tree_reconstruction_Harness_harnessqtvc: reconstruction of a
-- binary tree from the leaf-depth list [1, 3, 3, 2], asserting uniqueness of
-- the reconstructed tree and the non-impossibility of reconstruction. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module vstte12_tree_reconstruction_Harness_harnessqtvc where

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

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

zeroZ oneZ twoZ threeZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Tree : Set where
  Leaf : Tree
  Node : Tree → Tree → Tree

depths : Int → Tree → List Int
depths d Leaf = d ∷ []
depths d (Node l r) =
  depths (addInt d oneZ) l ++ depths (addInt d oneZ) r

inputDepths : List Int
inputDepths = oneZ ∷ threeZ ∷ threeZ ∷ twoZ ∷ []

expectedTree : Tree
expectedTree = Node Leaf (Node (Node Leaf Leaf) Leaf)

harness'vc : Set
harness'vc =
  ((result : Tree) →
    depths zeroZ result ≡ inputDepths →
    result ≡ expectedTree) ∧
  Not ((t : Tree) → Not (depths zeroZ t ≡ inputDepths))
