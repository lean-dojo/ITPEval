-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/pairing_heap_PairingHeap_delete_minqtvc: the pairing-heap
-- delete-minimum verification condition preserving heap order, size, and
-- element multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module pairing_heap_PairingHeap_delete_minqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_ _≢_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

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

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

module PairingHeapTheory
  (Elt : Set)
  (eltDefault : Elt)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (le : Elt → Elt → Set)
  (leRefl : (x : Elt) → le x x)
  (leTrans :
    (x y z : Elt) → le x y → le y z → le x z)
  (leTotal : (x y : Elt) → le x y ∨ le y x)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  mutual
    data RawHeap : Set where
      Empty : RawHeap
      nonempty : Tree → RawHeap

    data Tree : Set where
      tree : Elt → List Tree → Tree

  mutual
    sizeHeap : RawHeap → Int
    sizeHeap Empty = zeroZ
    sizeHeap (nonempty t) = sizeTree t

    sizeTree : Tree → Int
    sizeTree (tree root children) =
      addInt oneZ (sizeList children)

    sizeList : List Tree → Int
    sizeList [] = zeroZ
    sizeList (t ∷ rest) =
      addInt (sizeTree t) (sizeList rest)

  mutual
    occHeap : Elt → RawHeap → Int
    occHeap sought Empty = zeroZ
    occHeap sought (nonempty t) = occTree sought t

    occTree : Elt → Tree → Int
    occTree sought (tree root children)
      with decide (sought ≡ root)
    ... | yes equality =
      addInt oneZ (occList sought children)
    ... | no inequality =
      addInt zeroZ (occList sought children)

    occList : Elt → List Tree → Int
    occList sought [] = zeroZ
    occList sought (t ∷ rest) =
      addInt (occTree sought t) (occList sought rest)

  leTree : Elt → Tree → Set
  leTree lower (tree root children) = le lower root

  leRoots : Elt → List Tree → Set
  leRoots lower [] = ⊤
  leRoots lower (t ∷ rest) =
    leTree lower t ∧ leRoots lower rest

  mutual
    isHeap : RawHeap → Set
    isHeap Empty = ⊤
    isHeap (nonempty t) = isHeapTree t

    isHeapTree : Tree → Set
    isHeapTree (tree root children) =
      leRoots root children ∧ isHeapList children

    isHeapList : List Tree → Set
    isHeapList [] = ⊤
    isHeapList (t ∷ rest) =
      isHeapTree t ∧ isHeapList rest

  record Heap : Set where
    constructor heapValue
    field
      raw       : RawHeap
      invariant : isHeap raw

  open Heap public

  minimumTree : Tree → Elt
  minimumTree (tree root children) = root

  minimum : RawHeap → Elt
  minimum Empty = eltDefault
  minimum (nonempty t) = minimumTree t

  childrenAreHeaps : RawHeap → Set
  childrenAreHeaps Empty = ⊥
  childrenAreHeaps (nonempty (tree root children)) =
    isHeapList children

  resultPremise : RawHeap → Heap → Set
  resultPremise Empty result = ⊥
  resultPremise
    (nonempty (tree root children))
    result =
      sizeHeap (raw result) ≡ sizeList children ∧
      ((x : Elt) →
        occHeap x (raw result) ≡ occList x children)

  preservesOtherOccurrences : Elt → Heap → Heap → Set
  preservesOtherOccurrences removed result original =
    (y : Elt) →
    y ≢ removed →
    occHeap y (raw result) ≡ occHeap y (raw original)

  resultConclusion : Heap → Heap → Set
  resultConclusion original result =
    occHeap (minimum (raw original)) (raw result) ≡
      subtractInt
        (occHeap (minimum (raw original)) (raw original))
        oneZ ∧
    preservesOtherOccurrences
      (minimum (raw original))
      result
      original ∧
    sizeHeap (raw result) ≡
      subtractInt (sizeHeap (raw original)) oneZ

  delete-min'vc : Set
  delete-min'vc =
    (hh : Heap) →
    zeroZ <Z sizeHeap (raw hh) →
    childrenAreHeaps (raw hh) ∧
    ((result : Heap) →
      resultPremise (raw hh) result →
      resultConclusion hh result)
