-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/skew_heaps_HeapSort_heapsortqtvc: the skew-heap heapsort verification
-- condition preserving heap size and multiplicities while establishing
-- sortedness and permutation. This file contains no proof.

{-# OPTIONS --safe #-}

module skew_heaps_HeapSort_heapsortqtvc where

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

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

module SkewHeapSortTheory
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

  record Array : Set where
    constructor array
    field
      arrayLength : Nat
      elements    : Int → Elt

  open Array

  lengthZ : Array → Int
  lengthZ xs = natToInt (arrayLength xs)

  nthElt : Array → Int → Elt
  nthElt xs index = elements xs index

  nthFunction : Array → Int → Elt
  nthFunction xs index = nthElt xs index

  updateFunction : (Int → Elt) → Int → Elt → Int → Elt
  updateFunction values index value query with intEqual query index
  ... | true = value
  ... | false = values query

  setAt : Array → Int → Elt → Array
  setAt xs index value =
    array
      (arrayLength xs)
      (updateFunction (elements xs) index value)

  equalAt : Array → Elt → Int → Bool
  equalAt xs value index with decide (nthElt xs index ≡ value)
  ... | yes equality = true
  ... | no inequality = false

  countFrom : (Int → Bool) → Int → Nat → Nat
  countFrom predicate start zero = zero
  countFrom predicate start (suc count) with predicate start
  ... | true =
    suc (countFrom predicate (addInt start oneZ) count)
  ... | false =
    countFrom predicate (addInt start oneZ) count

  mapOcc : Elt → Array → Int → Int → Int
  mapOcc value xs lower upper =
    natToInt
      (countFrom
        (equalAt xs value)
        lower
        (toNat (subtractInt upper lower)))

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

  mem : Elt → Tree → Set
  mem value tree = zeroZ <Z occ value tree

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

  minimum : Tree → Elt
  minimum Empty = eltDefault
  minimum (Node l root r) = root

  empty : Tree
  empty = Empty

  sortedSub : Array → Int → Int → Set
  sortedSub xs lower upper =
    (i₁ i₂ : Int) →
    ((lower ≤Z i₁) ∧ (i₁ <Z i₂) ∧ (i₂ <Z upper)) →
    le (nthElt xs i₁) (nthElt xs i₂)

  sorted : Array → Set
  sorted xs = sortedSub xs zeroZ (lengthZ xs)

  permutAll : Array → Array → Set
  permutAll original current =
    arrayLength original ≡ arrayLength current ∧
    ((e : Elt) →
      mapOcc e original zeroZ (lengthZ original) ≡
        mapOcc e current zeroZ (lengthZ current))

  occurrenceBalance :
    Array → Int → Int → Tree → Int → Set
  occurrenceBalance original lower upper tree totalUpper =
    (e : Elt) →
    addInt (mapOcc e original lower upper) (occ e tree) ≡
      mapOcc e original zeroZ totalUpper

  prefixBelowHeap : Array → Tree → Int → Set
  prefixBelowHeap current tree upper =
    (j : Int) →
    ((zeroZ ≤Z j) ∧ (j <Z upper)) →
    (e : Elt) →
    mem e tree →
    le (nthElt current j) e

  sortInvariant :
    Array →
    Array →
    Tree →
    Int →
    Int →
    Int →
    Set
  sortInvariant original current tree totalLength lastIndex i =
    ((zeroZ ≤Z i) ∧ (i ≤Z lastIndex)) ∧
    sortedSub current zeroZ i ∧
    (heap tree ∧ size tree ≡ subtractInt totalLength i) ∧
    prefixBelowHeap current tree i ∧
    ((e : Elt) →
      addInt (mapOcc e current zeroZ i) (occ e tree) ≡
        mapOcc e original zeroZ totalLength)

  removePremise : Tree → Tree → Set
  removePremise original reduced =
    heap reduced ∧
    occ (minimum original) reduced ≡
      subtractInt (occ (minimum original) original) oneZ ∧
    ((e : Elt) →
      e ≢ minimum original →
      occ e reduced ≡ occ e original) ∧
    size reduced ≡ subtractInt (size original) oneZ

  nextSortInvariant :
    Array →
    Array →
    Tree →
    Int →
    Int →
    Set
  nextSortInvariant original updated reduced totalLength i =
    sortedSub updated zeroZ (addInt i oneZ) ∧
    (heap reduced ∧
      size reduced ≡
        subtractInt totalLength (addInt i oneZ)) ∧
    prefixBelowHeap updated reduced (addInt i oneZ) ∧
    ((e : Elt) →
      addInt
        (mapOcc e updated zeroZ (addInt i oneZ))
        (occ e reduced) ≡
      mapOcc e original zeroZ totalLength)

  sortStep :
    Array →
    Array →
    Tree →
    Int →
    Int →
    Int →
    Set
  sortStep original current tree totalLength lastIndex i =
    sortInvariant original current tree totalLength lastIndex i →
    (heap tree ∧ zeroZ <Z size tree) ∧
    (let chosen = minimum tree
         updated = setAt current i chosen
     in
     ((zeroZ ≤Z i) ∧ (i <Z lengthZ current)) ∧
     ((arrayLength updated ≡ arrayLength current) →
      ((query : Int) →
        nthFunction updated query ≡
          updateFunction (nthFunction current) i chosen query) →
      (heap tree ∧ zeroZ <Z size tree) ∧
      ((reduced : Tree) →
        removePremise tree reduced →
        nextSortInvariant
          original updated reduced totalLength i)))

  initialSortInvariant :
    Array → Tree → Int → Set
  initialSortInvariant original tree totalLength =
    sortedSub original zeroZ zeroZ ∧
    (heap tree ∧
      size tree ≡ subtractInt totalLength zeroZ) ∧
    prefixBelowHeap original tree zeroZ ∧
    ((e : Elt) →
      addInt (mapOcc e original zeroZ zeroZ) (occ e tree) ≡
        mapOcc e original zeroZ totalLength)

  finalSortInvariant :
    Array →
    Array →
    Tree →
    Int →
    Int →
    Set
  finalSortInvariant original current tree totalLength lastIndex =
    sortedSub current zeroZ (addInt lastIndex oneZ) ∧
    (heap tree ∧
      size tree ≡
        subtractInt totalLength (addInt lastIndex oneZ)) ∧
    prefixBelowHeap current tree (addInt lastIndex oneZ) ∧
    ((e : Elt) →
      addInt
        (mapOcc e current zeroZ (addInt lastIndex oneZ))
        (occ e tree) ≡
      mapOcc e original zeroZ totalLength)

  sortLoopAndExit :
    Array →
    Array →
    Tree →
    Int →
    Int →
    Set
  sortLoopAndExit original current tree totalLength lastIndex =
    ((i : Int) →
      sortStep original current tree totalLength lastIndex i) ∧
    (finalSortInvariant
      original current tree totalLength lastIndex →
      sorted current ∧ permutAll original current)

  sortWork :
    Array → Tree → Int → Int → Set
  sortWork original initialTree totalLength lastIndex =
    initialSortInvariant original initialTree totalLength ∧
    ((tree : Tree) →
      (current : Array) →
      arrayLength current ≡ arrayLength original →
      sortLoopAndExit
        original current tree totalLength lastIndex)

  sortingPhase : Array → Tree → Int → Set
  sortingPhase original initialTree totalLength =
    let lastIndex = subtractInt totalLength oneZ
    in
    ((zeroZ ≤Z addInt lastIndex oneZ) →
      sortWork original initialTree totalLength lastIndex) ∧
    ((addInt lastIndex oneZ <Z zeroZ) →
      sorted original ∧ permutAll original original)

  buildInitial : Array → Int → Set
  buildInitial original totalLength =
    (heap empty ∧ size empty ≡ zeroZ) ∧
    occurrenceBalance original zeroZ totalLength empty totalLength

  buildInvariant :
    Array → Tree → Int → Int → Set
  buildInvariant original tree totalLength lastIndex =
    ((zeroZ ≤Z size tree) ∧ (size tree ≤Z lastIndex)) ∧
    heap tree ∧
    occurrenceBalance
      original (size tree) totalLength tree totalLength

  addPremise : Elt → Tree → Tree → Set
  addPremise inserted original grown =
    heap grown ∧
    occ inserted grown ≡ addInt (occ inserted original) oneZ ∧
    ((e : Elt) →
      e ≢ inserted →
      occ e grown ≡ occ e original) ∧
    size grown ≡ addInt (size original) oneZ

  buildStep : Array → Tree → Int → Set
  buildStep original tree totalLength =
    ((zeroZ ≤Z size tree) ∧
      (size tree <Z lengthZ original)) ∧
    (let inserted = nthElt original (size tree)
     in
     heap tree ∧
     ((grown : Tree) →
       addPremise inserted tree grown →
       (heap grown ∧
         size grown ≡ addInt (size tree) oneZ) ∧
       occurrenceBalance
         original
         (addInt (size tree) oneZ)
         totalLength
         grown
         totalLength))

  buildFinalInvariant :
    Array → Tree → Int → Int → Set
  buildFinalInvariant original tree totalLength lastIndex =
    (heap tree ∧
      size tree ≡ addInt lastIndex oneZ) ∧
    occurrenceBalance
      original
      (addInt lastIndex oneZ)
      totalLength
      tree
      totalLength

  buildLoopBody :
    Array → Tree → Int → Int → Set
  buildLoopBody original tree totalLength lastIndex =
    (buildInvariant original tree totalLength lastIndex →
      buildStep original tree totalLength) ∧
    (buildFinalInvariant original tree totalLength lastIndex →
      sortingPhase original tree totalLength)

  buildWork : Array → Int → Int → Set
  buildWork original totalLength lastIndex =
    buildInitial original totalLength ∧
    ((tree : Tree) →
      buildLoopBody original tree totalLength lastIndex)

  heapSortVC : Array → Set
  heapSortVC original =
    let totalLength = lengthZ original
        lastIndex = subtractInt totalLength oneZ
    in
    ((zeroZ ≤Z addInt lastIndex oneZ) →
      buildWork original totalLength lastIndex) ∧
    ((addInt lastIndex oneZ <Z zeroZ) →
      sortingPhase original empty totalLength)

  heapsort'vc : Set
  heapsort'vc =
    (original : Array) →
    heapSortVC original
