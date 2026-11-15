-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/braun_trees_BraunHeaps_addqtvc: the Braun-heap insertion
-- verification condition preserving heap order, Braun balance, tree size,
-- and element multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module braun_trees_BraunHeaps_addqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≢_
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

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

module BraunHeapTheory
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
  size (Node l x r) =
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
  initialObligation whole@(Node l y r) =
    childMatchesRight whole r ∧
    heap r ∧
    inv r

  preservesOtherOccurrences : Elt → Tree → Tree → Set
  preservesOtherOccurrences distinguished result original =
    (e : Elt) →
    e ≢ distinguished →
    occ e result ≡ occ e original

  recursiveResult :
    Tree → Elt → Elt → Tree → Tree → Set
  recursiveResult result inserted oldRoot leftTree rightTree =
    IfDec
      (decide (le inserted oldRoot))
      (Exists Tree λ o1 →
        (heap o1 ∧
         inv o1 ∧
         occ oldRoot o1 ≡ addInt (occ oldRoot rightTree) oneZ ∧
         preservesOtherOccurrences oldRoot o1 rightTree ∧
         size o1 ≡ addInt (size rightTree) oneZ) ∧
        result ≡ Node o1 inserted leftTree)
      (Exists Tree λ o1 →
        (heap o1 ∧
         inv o1 ∧
         occ inserted o1 ≡ addInt (occ inserted rightTree) oneZ ∧
         preservesOtherOccurrences inserted o1 rightTree ∧
         size o1 ≡ addInt (size rightTree) oneZ) ∧
        result ≡ Node o1 oldRoot leftTree)

  resultPremise : Tree → Elt → Tree → Set
  resultPremise Empty inserted result =
    result ≡ Node Empty inserted Empty
  resultPremise (Node leftTree oldRoot rightTree) inserted result =
    recursiveResult result inserted oldRoot leftTree rightTree

  resultConclusion : Tree → Elt → Tree → Set
  resultConclusion original inserted result =
    heap result ∧
    inv result ∧
    occ inserted result ≡ addInt (occ inserted original) oneZ ∧
    preservesOtherOccurrences inserted result original ∧
    size result ≡ addInt (size original) oneZ

  add'vc : Set
  add'vc =
    (t : Tree) →
    (x : Elt) →
    heap t →
    inv t →
    initialObligation t ∧
    ((result : Tree) →
      resultPremise t x result →
      resultConclusion t x result)
