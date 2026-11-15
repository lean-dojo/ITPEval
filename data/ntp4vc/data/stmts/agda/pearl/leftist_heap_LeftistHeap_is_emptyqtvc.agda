-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/leftist_heap_LeftistHeap_is_emptyqtvc: the leftist-heap emptiness
-- verification condition equating a shape-derived Boolean result with zero
-- integer tree size. This file contains no proof.

{-# OPTIONS --safe #-}

module leftist_heap_LeftistHeap_is_emptyqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 2 _∨_
infix 1 _↔_

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

module LeftistHeapIsEmptyTheory
  (Elt : Set)
  (eltDefault : Elt)
  (T : Set)
  (tDefault : T)
  (le : Elt → Elt → Set)
  (leRefl : (x : Elt) → le x x)
  (leTrans :
    (x y z : Elt) → le x y → le y z → le x z)
  (leTotal : (x y : Elt) → le x y ∨ le y x)
  where

  data Tree : Set where
    Empty : Tree
    Node  : Int → Tree → Elt → Tree → Tree

  size : Tree → Int
  size Empty = zeroZ
  size (Node annotation l root r) =
    addInt (addInt oneZ (size l)) (size r)

  resultPremise : Tree → Bool → Set
  resultPremise Empty result = result ≡ true
  resultPremise (Node annotation l root r) result = result ≡ false

  is-empty'vc : Set
  is-empty'vc =
    (h : Tree) →
    (result : Bool) →
    resultPremise h result →
    (result ≡ true) ↔ (size h ≡ zeroZ)
