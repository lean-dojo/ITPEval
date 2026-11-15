-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/binomial_heap_BinomialHeap_extract_minqtvc: the binomial-heap
-- minimum extraction verification condition preserving heap order, rank
-- invariants, and element multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module binomial_heap_BinomialHeap_extract_minqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _≢_
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

append : {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = append (reverse xs) (x ∷ [])

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

  extractionPremise : List Tree → Tree → List Tree → Set
  extractionPremise h t h′ =
    heaps (t ∷ []) ∧
    heaps h′ ∧
    inv zeroZ h′ ∧
    leRoots (elem t) h ∧
    binomialTree t ∧
    ((x : Elt) →
      occ x h ≡
        addInt
          (occ x (t ∷ []))
          (occ x h′))

  reversedChildrenValid : Tree → List Tree → Set
  reversedChildrenValid t h′ =
    heaps (reverse (children t)) ∧
    inv zeroZ (reverse (children t)) ∧
    heaps h′ ∧
    inv zeroZ h′

  mergedHeapConclusion :
    List Tree → Tree → List Tree → List Tree → Set
  mergedHeapConclusion h t h′ h′1 =
    heaps h′1 ∧
    inv zeroZ h′1 ∧
    occ (elem t) h′1 ≡
      subtractInt (occ (elem t) h) oneZ ∧
    ((x : Elt) →
      x ≢ elem t →
      occ x h′1 ≡ occ x h)

  extract-min'vc : Set
  extract-min'vc =
    (h : List Tree) →
    heaps h →
    inv zeroZ h →
    h ≢ [] →
    heaps h ∧
    inv zeroZ h ∧
    h ≢ [] ∧
    ((t : Tree) →
      (h′ : List Tree) →
      extractionPremise h t h′ →
      reversedChildrenValid t h′ ∧
      ((h′1 : List Tree) →
        heaps h′1 ∧
        inv zeroZ h′1 ∧
        ((x : Elt) →
          occ x h′1 ≡
            addInt
              (occ x (reverse (children t)))
              (occ x h′)) →
        mergedHeapConclusion h t h′ h′1))
