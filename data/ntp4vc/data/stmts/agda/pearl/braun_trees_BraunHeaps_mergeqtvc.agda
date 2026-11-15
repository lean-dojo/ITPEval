-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/braun_trees_BraunHeaps_mergeqtvc: the Braun-heap merge verification
-- condition preserving heap order, Braun balance, tree size, and element
-- multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module braun_trees_BraunHeaps_mergeqtvc where

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

  inv : Tree → Set
  inv Empty = ⊤
  inv (Node l root r) =
    (size l ≡ size r ∨
     size l ≡ addInt (size r) oneZ) ∧
    inv l ∧
    inv r

  minimum : Tree → Elt
  minimum Empty = eltDefault
  minimum (Node l root r) = root

  occurrenceSum : Tree → Tree → Tree → Set
  occurrenceSum result leftTree rightTree =
    (e : Elt) →
    occ e result ≡ addInt (occ e leftTree) (occ e rightTree)

  preservesOtherOccurrences : Elt → Tree → Tree → Set
  preservesOtherOccurrences distinguished result original =
    (e : Elt) →
    e ≢ distinguished →
    occ e result ≡ occ e original

  extractionPremise : Tree → Elt → Tree → Set
  extractionPremise original extracted reduced =
    heap reduced ∧
    inv reduced ∧
    size reduced ≡ subtractInt (size original) oneZ ∧
    occ extracted reduced ≡
      subtractInt (occ extracted original) oneZ ∧
    preservesOtherOccurrences extracted reduced original

  initialObligation : Tree → Tree → Set
  initialObligation l Empty = ⊤
  initialObligation Empty (Node rl rr rr′) = ⊥
  initialObligation
    l@(Node leftLeft leftRoot leftRight)
    r@(Node rightLeft rightRoot rightRight) =
      IfDec
        (decide (le leftRoot rightRoot))
        ((zeroZ ≤Z addInt (size l) (size r) ∧
          addInt (size leftLeft) (size leftRight) <Z
            addInt (size l) (size r)) ∧
         (heap leftLeft ∧ heap leftRight) ∧
         (inv leftLeft ∧ inv leftRight) ∧
         size leftRight ≤Z size leftLeft ∧
         size leftLeft ≤Z addInt (size leftRight) oneZ)
        ((heap l ∧ inv l ∧ zeroZ <Z size l) ∧
         ((extracted : Elt) →
          (reduced : Tree) →
          extractionPremise l extracted reduced →
          heap r ∧ inv r ∧ zeroZ <Z size r))

  rebuiltRightPremise : Elt → Tree → Tree → Set
  rebuiltRightPremise extracted original rebuilt =
    heap rebuilt ∧
    inv rebuilt ∧
    IfDec
      (decide (extracted ≡ minimum original))
      (occ extracted rebuilt ≡ occ extracted original)
      (occ extracted rebuilt ≡
         addInt (occ extracted original) oneZ ∧
       occ (minimum original) rebuilt ≡
         subtractInt (occ (minimum original) original) oneZ) ∧
    ((other : Elt) →
      other ≢ extracted →
      other ≢ minimum original →
      occ other rebuilt ≡ occ other original) ∧
    size rebuilt ≡ size original

  resultPremise : Tree → Tree → Tree → Set
  resultPremise l Empty result = result ≡ l
  resultPremise Empty (Node rl rr rr′) result = ⊥
  resultPremise
    l@(Node leftLeft leftRoot leftRight)
    r@(Node rightLeft rightRoot rightRight)
    result =
      IfDec
        (decide (le leftRoot rightRoot))
        (Exists Tree λ mergedChildren →
          (heap mergedChildren ∧
           inv mergedChildren ∧
           occurrenceSum mergedChildren leftLeft leftRight ∧
           size mergedChildren ≡
             addInt (size leftLeft) (size leftRight)) ∧
          result ≡ Node r leftRoot mergedChildren)
        (Exists Elt λ extracted →
          Exists Tree λ reducedLeft →
            extractionPremise l extracted reducedLeft ∧
            (Exists Tree λ rebuiltRight →
              rebuiltRightPremise extracted r rebuiltRight ∧
              result ≡ Node rebuiltRight rightRoot reducedLeft))

  resultConclusion : Tree → Tree → Tree → Set
  resultConclusion l r result =
    heap result ∧
    inv result ∧
    occurrenceSum result l r ∧
    size result ≡ addInt (size l) (size r)

  merge'vc : Set
  merge'vc =
    (l : Tree) →
    (r : Tree) →
    heap l →
    heap r →
    inv l →
    inv r →
    size r ≤Z size l →
    size l ≤Z addInt (size r) oneZ →
    initialObligation l r ∧
    ((result : Tree) →
      resultPremise l r result →
      resultConclusion l r result)
