-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/braun_trees_BraunHeaps_fast_sizeqtvc: the Braun-tree fast-size
-- verification condition relating the recursive size computation to the
-- Braun balance invariant. This file contains no proof.

{-# OPTIONS --safe #-}

module braun_trees_BraunHeaps_fast_sizeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

module BraunSizeTheory
  (Elt : Set)
  (eltDefault : Elt)
  where

  data Tree : Set where
    Empty : Tree
    Node  : Tree → Elt → Tree → Tree

  size : Tree → Int
  size Empty = zeroZ
  size (Node l root r) =
    addInt (addInt oneZ (size l)) (size r)

  inv : Tree → Set
  inv Empty = ⊤
  inv (Node l root r) =
    (size l ≡ size r ∨
     size l ≡ addInt (size r) oneZ) ∧
    inv l ∧
    inv r

  childMatchesRight : Tree → Tree → Set
  childMatchesRight Empty expectedRight = ⊥
  childMatchesRight (Node first root second) expectedRight =
    first ≡ expectedRight ∨ second ≡ expectedRight

  initialObligation : Tree → Set
  initialObligation Empty = ⊤
  initialObligation whole@(Node l root r) =
    (childMatchesRight whole r ∧ inv r) ∧
    let m = size r
    in
    inv l ∧
    zeroZ ≤Z m ∧
    m ≤Z size l ∧
    size l ≤Z addInt m oneZ

  resultPremise : Tree → Int → Set
  resultPremise Empty result =
    result ≡ zeroZ
  resultPremise (Node l root r) result =
    let m = size r
    in
    Exists Int λ o1 →
      size l ≡ addInt m o1 ∧
      result ≡
        addInt
          (addInt oneZ (multiplyInt twoZ m))
          o1

  resultConclusion : Tree → Set
  resultConclusion t =
    (result : Int) →
    resultPremise t result →
    result ≡ size t

  fast-size'vc : Set
  fast-size'vc =
    (t : Tree) →
    inv t →
    initialObligation t ∧
    resultConclusion t
