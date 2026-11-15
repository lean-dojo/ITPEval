-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/braun_trees_BraunHeaps_extractqtvc: the Braun-heap extraction
-- verification condition preserving heap order, Braun balance, tree size,
-- and element multiplicities. This file contains no proof.

{-# OPTIONS --safe #-}

module braun_trees_BraunHeaps_extractqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
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

  childMatchesLeft : Tree → Tree → Set
  childMatchesLeft Empty expectedLeft = ⊥
  childMatchesLeft (Node first root second) expectedLeft =
    first ≡ expectedLeft ∨ second ≡ expectedLeft

  initialObligation : Tree → Set
  initialObligation Empty = ⊥
  initialObligation (Node Empty y r) = ⊤
  initialObligation whole@(Node leftTree@(Node _ _ _) y rightTree) =
    childMatchesLeft whole leftTree ∧
    heap leftTree ∧
    inv leftTree ∧
    zeroZ <Z size leftTree

  preservesOtherOccurrences : Elt → Tree → Tree → Set
  preservesOtherOccurrences distinguished result original =
    (x : Elt) →
    x ≢ distinguished →
    occ x result ≡ occ x original

  extractionPremise : Tree → Elt → Tree → Set
  extractionPremise Empty extracted result = ⊥
  extractionPremise (Node Empty root rightTree) extracted result =
    extracted ≡ root ∧
    result ≡ Empty
  extractionPremise
    (Node leftTree@(Node _ _ _) root rightTree)
    extracted
    result =
      Exists Tree λ reducedLeft →
        (heap reducedLeft ∧
         inv reducedLeft ∧
         size reducedLeft ≡ subtractInt (size leftTree) oneZ ∧
         occ extracted reducedLeft ≡
           subtractInt (occ extracted leftTree) oneZ ∧
         preservesOtherOccurrences extracted reducedLeft leftTree) ∧
        result ≡ Node rightTree root reducedLeft

  extractionConclusion : Tree → Elt → Tree → Set
  extractionConclusion original extracted result =
    heap result ∧
    inv result ∧
    size result ≡ subtractInt (size original) oneZ ∧
    occ extracted result ≡ subtractInt (occ extracted original) oneZ ∧
    preservesOtherOccurrences extracted result original

  extract'vc : Set
  extract'vc =
    (t : Tree) →
    heap t →
    inv t →
    zeroZ <Z size t →
    initialObligation t ∧
    ((extracted : Elt) →
      (result : Tree) →
      extractionPremise t extracted result →
      extractionConclusion t extracted result)
