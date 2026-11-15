-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/leftist_heap_LeftistHeap_delete_minqtvc: the leftist-heap delete-minimum
-- verification condition preserving heap order, leftist ranks, tree size, and
-- element multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module leftist_heap_LeftistHeap_delete_minqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<Z_ _≤Z_ _≢_
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

minInt : Int → Int → Int
minInt x y with intLessOrEqual x y
... | true = x
... | false = y

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

module LeftistHeapTheory
  (Elt : Set)
  (eltDefault : Elt)
  (T : Set)
  (tDefault : T)
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
    Node  : Int → Tree → Elt → Tree → Tree

  size : Tree → Int
  size Empty = zeroZ
  size (Node annotation l root r) =
    addInt (addInt oneZ (size l)) (size r)

  occ : Elt → Tree → Int
  occ sought Empty = zeroZ
  occ sought (Node annotation l root r) with decide (sought ≡ root)
  ... | yes equality =
    addInt (addInt oneZ (occ sought l)) (occ sought r)
  ... | no inequality =
    addInt (addInt zeroZ (occ sought l)) (occ sought r)

  mem : Elt → Tree → Set
  mem value tree = zeroZ <Z occ value tree

  leRoot : Elt → Tree → Set
  leRoot lower Empty = ⊤
  leRoot lower (Node annotation l root r) = le lower root

  isHeap : Tree → Set
  isHeap Empty = ⊤
  isHeap (Node annotation l root r) =
    leRoot root l ∧
    isHeap l ∧
    leRoot root r ∧
    isHeap r

  minimum : Tree → Elt
  minimum Empty = eltDefault
  minimum (Node annotation l root r) = root

  isMinimum : Elt → Tree → Set
  isMinimum candidate tree =
    mem candidate tree ∧
    ((value : Elt) → mem value tree → le candidate value)

  rank : Tree → Int
  rank Empty = zeroZ
  rank (Node annotation l root r) =
    addInt oneZ (minInt (rank l) (rank r))

  leftist : Tree → Set
  leftist Empty = ⊤
  leftist whole@(Node annotation l root r) =
    annotation ≡ rank whole ∧
    leftist l ∧
    leftist r ∧
    rank r ≤Z rank l

  leftistHeap : Tree → Set
  leftistHeap tree = isHeap tree ∧ leftist tree

  childrenAreLeftistHeaps : Tree → Set
  childrenAreLeftistHeaps Empty = ⊥
  childrenAreLeftistHeaps (Node annotation l root r) =
    leftistHeap l ∧ leftistHeap r

  resultPremise : Tree → Tree → Set
  resultPremise Empty result = ⊥
  resultPremise (Node annotation l root r) result =
    size result ≡ addInt (size l) (size r) ∧
    ((value : Elt) →
      occ value result ≡ addInt (occ value l) (occ value r)) ∧
    leftistHeap result

  preservesOtherOccurrences : Elt → Tree → Tree → Set
  preservesOtherOccurrences removed result original =
    (value : Elt) →
    value ≢ removed →
    occ value result ≡ occ value original

  resultConclusion : Tree → Tree → Set
  resultConclusion original result =
    occ (minimum original) result ≡
      subtractInt (occ (minimum original) original) oneZ ∧
    preservesOtherOccurrences (minimum original) result original ∧
    size result ≡ subtractInt (size original) oneZ ∧
    leftistHeap result

  delete-min'vc : Set
  delete-min'vc =
    (h : Tree) →
    zeroZ <Z size h →
    leftistHeap h →
    childrenAreLeftistHeaps h ∧
    ((result : Tree) →
      resultPremise h result →
      resultConclusion h result)
