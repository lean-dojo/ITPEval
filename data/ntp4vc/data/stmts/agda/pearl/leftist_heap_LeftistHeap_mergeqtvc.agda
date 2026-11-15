-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/leftist_heap_LeftistHeap_mergeqtvc: the leftist-heap merge verification
-- condition preserving heap order, leftist ranks, tree size, and element
-- multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module leftist_heap_LeftistHeap_mergeqtvc where

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

minInt : Int → Int → Int
minInt x y with intLessOrEqual x y
... | true = x
... | false = y

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

module LeftistHeapMergeTheory
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

  occurrenceSum : Tree → Tree → Tree → Set
  occurrenceSum result leftTree rightTree =
    (value : Elt) →
    occ value result ≡
      addInt (occ value leftTree) (occ value rightTree)

  recursivePremise : Tree → Tree → Tree → Set
  recursivePremise leftTree rightTree result =
    size result ≡ addInt (size leftTree) (size rightTree) ∧
    occurrenceSum result leftTree rightTree ∧
    leftistHeap result

  initialObligation : Tree → Tree → Set
  initialObligation h1 Empty = ⊤
  initialObligation Empty (Node rank2 l2 root2 r2) = ⊤
  initialObligation
    h1@(Node rank1 l1 root1 r1)
    h2@(Node rank2 l2 root2 r2) =
      IfDec
        (decide (le root1 root2))
        (((zeroZ ≤Z addInt (size h1) (size h2) ∧
           addInt (size r1) (size h2) <Z
             addInt (size h1) (size h2)) ∧
          leftistHeap r1 ∧
          leftistHeap h2) ∧
         ((o1 : Tree) →
          recursivePremise r1 h2 o1 →
          (leftistHeap o1 ∧ leftistHeap l1) ∧
          leRoot root1 l1 ∧
          leRoot root1 o1))
        (((zeroZ ≤Z addInt (size h1) (size h2) ∧
           addInt (size h1) (size r2) <Z
             addInt (size h1) (size h2)) ∧
          leftistHeap h1 ∧
          leftistHeap r2) ∧
         ((o1 : Tree) →
          recursivePremise h1 r2 o1 →
          (leftistHeap o1 ∧ leftistHeap l2) ∧
          leRoot root2 l2 ∧
          leRoot root2 o1))

  firstBranchResultPremise :
    Tree → Tree → Elt → Tree → Tree → Set
  firstBranchResultPremise l1 r1 root1 h2 result =
    Exists Tree λ o1 →
      recursivePremise r1 h2 o1 ∧
      leftistHeap result ∧
      minimum result ≡ root1 ∧
      size result ≡ addInt (addInt oneZ (size l1)) (size o1) ∧
      occ root1 result ≡
        addInt (addInt oneZ (occ root1 l1)) (occ root1 o1) ∧
      ((value : Elt) →
        root1 ≢ value →
        occ value result ≡
          addInt (occ value l1) (occ value o1))

  secondBranchResultPremise :
    Tree → Tree → Elt → Tree → Tree → Set
  secondBranchResultPremise h1 l2 root2 r2 result =
    Exists Tree λ o1 →
      recursivePremise h1 r2 o1 ∧
      leftistHeap result ∧
      minimum result ≡ root2 ∧
      size result ≡ addInt (addInt oneZ (size l2)) (size o1) ∧
      occ root2 result ≡
        addInt (addInt oneZ (occ root2 l2)) (occ root2 o1) ∧
      ((value : Elt) →
        root2 ≢ value →
        occ value result ≡
          addInt (occ value l2) (occ value o1))

  resultPremise : Tree → Tree → Tree → Set
  resultPremise h1 Empty result = result ≡ h1
  resultPremise Empty h2@(Node rank2 l2 root2 r2) result =
    result ≡ h2
  resultPremise
    h1@(Node rank1 l1 root1 r1)
    h2@(Node rank2 l2 root2 r2)
    result =
      IfDec
        (decide (le root1 root2))
        (firstBranchResultPremise l1 r1 root1 h2 result)
        (secondBranchResultPremise h1 l2 root2 r2 result)

  resultConclusion : Tree → Tree → Tree → Set
  resultConclusion h1 h2 result =
    size result ≡ addInt (size h1) (size h2) ∧
    occurrenceSum result h1 h2 ∧
    leftistHeap result

  merge'vc : Set
  merge'vc =
    (h1 : Tree) →
    (h2 : Tree) →
    leftistHeap h1 →
    leftistHeap h2 →
    initialObligation h1 h2 ∧
    ((result : Tree) →
      resultPremise h1 h2 result →
      resultConclusion h1 h2 result)
