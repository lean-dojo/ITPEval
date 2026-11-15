-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_tree_reconstruction_Harness_harness2qtvc: no binary tree has
-- the left-to-right leaf-depth list [1, 3, 2, 2] when its root is at depth zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module vstte12_tree_reconstruction_Harness_harness2qtvc where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≢_
infixr 5 _++_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

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
depths d (Node left right) =
  depths (addInt d oneZ) left ++
  depths (addInt d oneZ) right

harness2-vc : Set
harness2-vc =
  (x : Tree) →
  depths zeroZ x ≢ (oneZ ∷ threeZ ∷ twoZ ∷ twoZ ∷ [])
