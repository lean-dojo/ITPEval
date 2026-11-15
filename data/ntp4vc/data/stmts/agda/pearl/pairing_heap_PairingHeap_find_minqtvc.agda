-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/pairing_heap_PairingHeap_find_minqtvc: the pairing-heap find-minimum
-- verification condition showing that a positive-size heap is nonempty and
-- that its returned root is the abstract minimum. This file contains no proof.

{-# OPTIONS --safe #-}

module pairing_heap_PairingHeap_find_minqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_
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

module PairingHeapTheory
  (Elt : Set)
  (eltDefault : Elt)
  (le : Elt → Elt → Set)
  (leRefl : (x : Elt) → le x x)
  (leTrans :
    (x y z : Elt) → le x y → le y z → le x z)
  (leTotal : (x y : Elt) → le x y ∨ le y x)
  where

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

  nonemptyCase : RawHeap → Set
  nonemptyCase Empty = ⊥
  nonemptyCase (nonempty (tree root children)) = ⊤

  resultPremise : RawHeap → Elt → Set
  resultPremise Empty result = ⊥
  resultPremise
    (nonempty (tree root children))
    result =
      result ≡ root

  find-min'vc : Set
  find-min'vc =
    (hh : Heap) →
    zeroZ <Z sizeHeap (raw hh) →
    nonemptyCase (raw hh) ∧
    ((result : Elt) →
      resultPremise (raw hh) result →
      result ≡ minimum (raw hh))
