-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/binomial_heap_BinomialHeap_mergeqtvc: the binomial-heap merge
-- verification condition preserving heap order, rank invariants, and
-- element multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module binomial_heap_BinomialHeap_mergeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_
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

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

module BinomialHeapTheory
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
    tree : Elt → List Tree → Int → Tree

  elem : Tree → Elt
  elem (tree value descendants treeRank) = value

  children : Tree → List Tree
  children (tree value descendants treeRank) = descendants

  rank : Tree → Int
  rank (tree value descendants treeRank) = treeRank

  leRoots : Elt → List Tree → Set
  leRoots lower [] = ⊤
  leRoots lower (t ∷ rest) =
    le lower (elem t) ∧ leRoots lower rest

  heaps : List Tree → Set
  heaps [] = ⊤
  heaps (tree root descendants treeRank ∷ rest) =
    leRoots root descendants ∧
    heaps descendants ∧
    heaps rest

  occ : Elt → List Tree → Int
  occ sought [] = zeroZ
  occ sought (tree root descendants treeRank ∷ rest)
    with decide (sought ≡ root)
  ... | yes equality =
    addInt
      (addInt oneZ (occ sought descendants))
      (occ sought rest)
  ... | no inequality =
    addInt
      (addInt zeroZ (occ sought descendants))
      (occ sought rest)

  hasOrder : Int → List Tree → Set
  hasOrder expected [] = expected ≡ zeroZ
  hasOrder expected (tree root descendants treeRank ∷ rest) =
    treeRank ≡ subtractInt expected oneZ ∧
    hasOrder (subtractInt expected oneZ) descendants ∧
    hasOrder (subtractInt expected oneZ) rest

  binomialTree : Tree → Set
  binomialTree t =
    rank t ≡ natToInt (length (children t)) ∧
    hasOrder (rank t) (children t)

  inv : Int → List Tree → Set
  inv minimumRank [] = ⊤
  inv minimumRank (t ∷ rest) =
    minimumRank ≤Z rank t ∧
    binomialTree t ∧
    inv (addInt (rank t) oneZ) rest

  link : Tree → Tree → Tree
  link t1 t2 with decide (le (elem t1) (elem t2))
  ... | yes proof =
    tree
      (elem t1)
      (t2 ∷ children t1)
      (addInt (rank t1) oneZ)
  ... | no refutation =
    tree
      (elem t2)
      (t1 ∷ children t2)
      (addInt (rank t2) oneZ)

  tailMatches : List Tree → List Tree → Set
  tailMatches [] expectedTail = ⊥
  tailMatches (head ∷ actualTail) expectedTail =
    actualTail ≡ expectedTail

  occurrenceSum :
    List Tree → List Tree → List Tree → Set
  occurrenceSum result leftForest rightForest =
    (x : Elt) →
    occ x result ≡ addInt (occ x leftForest) (occ x rightForest)

  initialObligation : List Tree → List Tree → Set
  initialObligation h1 [] = ⊤
  initialObligation [] (x ∷ x1) = ⊤
  initialObligation (x2 ∷ x3) (x ∷ x1)
    with intLess (rank x2) (rank x)
  ... | true =
    let nextRank = addInt (rank x2) oneZ
    in
    tailMatches (x2 ∷ x3) x3 ∧
    heaps x3 ∧
    inv nextRank x3 ∧
    heaps (x ∷ x1) ∧
    inv nextRank (x ∷ x1)
  ... | false with intLess (rank x) (rank x2)
  ...   | true =
    let nextRank = addInt (rank x) oneZ
    in
    tailMatches (x ∷ x1) x1 ∧
    heaps (x2 ∷ x3) ∧
    inv nextRank (x2 ∷ x3) ∧
    heaps x1 ∧
    inv nextRank x1
  ...   | false =
    let nextRank = addInt (rank x2) oneZ
    in
    ((tailMatches (x2 ∷ x3) x3 ∨
      ((x2 ∷ x3) ≡ x3 ∧ tailMatches (x ∷ x1) x1)) ∧
     heaps x3 ∧
     inv nextRank x3 ∧
     heaps x1 ∧
     inv nextRank x1) ∧
    ((o2 : List Tree) →
      heaps o2 ∧
      inv nextRank o2 ∧
      occurrenceSum o2 x3 x1 →
      let linkedTree = link x2 x
      in
      heaps (linkedTree ∷ []) ∧
      binomialTree linkedTree ∧
      heaps o2 ∧
      inv (rank linkedTree) o2)

  resultPremise :
    List Tree → List Tree → List Tree → Set
  resultPremise result [] [] = result ≡ []
  resultPremise result (x2 ∷ x3) [] =
    result ≡ x2 ∷ x3
  resultPremise result [] (x ∷ x1) =
    result ≡ x ∷ x1
  resultPremise result (x2 ∷ x3) (x ∷ x1)
    with intLess (rank x2) (rank x)
  ... | true =
    Exists (List Tree) λ o1 →
      (heaps o1 ∧
       inv (addInt (rank x2) oneZ) o1 ∧
       occurrenceSum o1 x3 (x ∷ x1)) ∧
      result ≡ x2 ∷ o1
  ... | false with intLess (rank x) (rank x2)
  ...   | true =
    Exists (List Tree) λ o1 →
      (heaps o1 ∧
       inv (addInt (rank x) oneZ) o1 ∧
       occurrenceSum o1 (x2 ∷ x3) x1) ∧
      result ≡ x ∷ o1
  ...   | false =
    Exists (List Tree) λ o1 →
      (heaps o1 ∧
       inv (addInt (rank x2) oneZ) o1 ∧
       occurrenceSum o1 x3 x1) ∧
      let linkedTree = link x2 x
      in
      heaps result ∧
      inv (rank linkedTree) result ∧
      occurrenceSum result (linkedTree ∷ []) o1

  resultConclusion :
    Int → List Tree → List Tree → List Tree → Set
  resultConclusion minimumRank h1 h2 result =
    heaps result ∧
    inv minimumRank result ∧
    occurrenceSum result h1 h2

  merge'vc : Set
  merge'vc =
    (h1 : List Tree) →
    (k : Int) →
    (h2 : List Tree) →
    heaps h1 →
    inv k h1 →
    heaps h2 →
    inv k h2 →
    initialObligation h1 h2 ∧
    ((result : List Tree) →
      resultPremise result h1 h2 →
      resultConclusion k h1 h2 result)
