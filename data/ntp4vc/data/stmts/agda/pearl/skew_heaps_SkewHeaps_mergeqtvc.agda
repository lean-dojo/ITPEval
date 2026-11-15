-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/skew_heaps_SkewHeaps_mergeqtvc: the skew-heap merge verification
-- condition preserving heap order, tree size, and element multiplicities.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module skew_heaps_SkewHeaps_mergeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_ _≤Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

IfDec : {P : Set} → Dec P → Set → Set → Set
IfDec (yes _) when-true when-false = when-true
IfDec (no _) when-true when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

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

module SkewHeapMergeTheory
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

  data Tree : Set where
    Empty : Tree
    Node  : Tree → Elt → Tree → Tree

  size : Tree → Int
  size Empty = zeroZ
  size (Node l root r) =
    addInt (addInt oneZ (size l)) (size r)

  occ : Elt → Tree → Int
  occ sought Empty = zeroZ
  occ sought (Node l root r) with decide (root ≡ sought)
  ... | yes equality =
    addInt (addInt oneZ (occ sought l)) (occ sought r)
  ... | no inequality =
    addInt (addInt zeroZ (occ sought l)) (occ sought r)

  leRoot : Elt → Tree → Set
  leRoot lower Empty = ⊤
  leRoot lower (Node l root r) = le lower root

  heap : Tree → Set
  heap Empty = ⊤
  heap (Node l root r) =
    leRoot root l ∧
    heap l ∧
    leRoot root r ∧
    heap r

  occurrenceSum : Tree → Tree → Tree → Set
  occurrenceSum result firstTree secondTree =
    (e : Elt) →
    occ e result ≡
      addInt (occ e firstTree) (occ e secondTree)

  initialObligation : Tree → Tree → Set
  initialObligation t1 Empty = ⊤
  initialObligation Empty (Node l2 root2 r2) = ⊤
  initialObligation
    t1@(Node l1 root1 r1)
    t2@(Node l2 root2 r2) =
      IfDec
        (decide (le root1 root2))
        ((zeroZ ≤Z addInt (size t1) (size t2) ∧
          addInt (size r1) (size t2) <Z
            addInt (size t1) (size t2)) ∧
         heap r1 ∧
         heap t2)
        ((zeroZ ≤Z addInt (size t1) (size t2) ∧
          addInt (size r2) (size t1) <Z
            addInt (size t1) (size t2)) ∧
         heap r2 ∧
         heap t1)

  recursivePremise : Tree → Tree → Tree → Set
  recursivePremise result firstTree secondTree =
    heap result ∧
    occurrenceSum result firstTree secondTree ∧
    size result ≡ addInt (size firstTree) (size secondTree)

  resultPremise : Tree → Tree → Tree → Set
  resultPremise Empty Empty result = result ≡ Empty
  resultPremise t1@(Node l1 root1 r1) Empty result =
    result ≡ t1
  resultPremise Empty t2@(Node l2 root2 r2) result =
    result ≡ t2
  resultPremise
    t1@(Node l1 root1 r1)
    t2@(Node l2 root2 r2)
    result =
      IfDec
        (decide (le root1 root2))
        (Exists Tree λ merged →
          recursivePremise merged r1 t2 ∧
          result ≡ Node merged root1 l1)
        (Exists Tree λ merged →
          recursivePremise merged r2 t1 ∧
          result ≡ Node merged root2 l2)

  resultConclusion : Tree → Tree → Tree → Set
  resultConclusion t1 t2 result =
    heap result ∧
    occurrenceSum result t1 t2 ∧
    size result ≡ addInt (size t1) (size t2)

  merge'vc : Set
  merge'vc =
    (t1 : Tree) →
    (t2 : Tree) →
    heap t1 →
    heap t2 →
    initialObligation t1 t2 ∧
    ((result : Tree) →
      resultPremise t1 t2 result →
      resultConclusion t1 t2 result)
