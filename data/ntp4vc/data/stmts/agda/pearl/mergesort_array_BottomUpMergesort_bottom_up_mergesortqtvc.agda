-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/mergesort_array_BottomUpMergesort_bottom_up_mergesortqtvc: the
-- bottom-up mergesort verification condition, preserving permutation and
-- sorted runs through its outer and inner merge loops. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module mergesort_array_BottomUpMergesort_bottom_up_mergesortqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤N_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

_≤N_ : Nat → Nat → Set
x ≤N y = natLessOrEqual x y ≡ true

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

minInt : Int → Int → Int
minInt x y with intLessOrEqual x y
... | true = x
... | false = y

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

take : {A : Set} → Nat → List A → List A
take zero _ = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

slice : {A : Set} → List A → Nat → Nat → List A
slice xs lower upper =
  take (natSubtract upper lower) (drop lower xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

data Perm {A : Set} : List A → List A → Set where
  permNil :
    Perm [] []

  permKeep :
    {x : A} {xs ys : List A} →
    Perm xs ys →
    Perm (x ∷ xs) (x ∷ ys)

  permSwap :
    (x y : A) →
    (xs : List A) →
    Perm (x ∷ y ∷ xs) (y ∷ x ∷ xs)

  permTrans :
    {xs ys zs : List A} →
    Perm xs ys →
    Perm ys zs →
    Perm xs zs

permutSub : {A : Set} → List A → List A → Nat → Nat → Set
permutSub xs ys lower upper =
  (length xs ≡ length ys) ∧
  ((zero ≤N lower) ∧ (lower ≤N length xs)) ∧
  ((zero ≤N upper) ∧ (upper ≤N length xs)) ∧
  Perm (slice xs lower upper) (slice ys lower upper)

module BottomUpMergesortTheory
  (Elt : Set)
  (eltDefault : Elt)
  (le : Elt → Elt → Set)
  (leRefl : (x : Elt) → le x x)
  (leTrans :
    (x y z : Elt) → le x y → le y z → le x z)
  (leTotal : (x y : Elt) → le x y ∨ le y x)
  where

  nthElt : List Elt → Int → Elt
  nthElt xs index = nthDefault eltDefault (toNat index) xs

  sortedSub : List Elt → Int → Int → Set
  sortedSub xs lower upper =
    (i₁ i₂ : Int) →
    ((lower ≤Z i₁) ∧ (i₁ <Z i₂) ∧ (i₂ <Z upper)) →
    le (nthElt xs i₁) (nthElt xs i₂)

  sorted : List Elt → Set
  sorted xs = sortedSub xs zeroZ (lengthZ xs)

  BlocksSorted :
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Set
  BlocksSorted xs blockLength lower upper n =
    (k : Int) →
    let l = multiplyInt k blockLength
    in
    ((lower ≤Z l) ∧ (l <Z upper)) →
    sortedSub xs l (minInt n (addInt l blockLength))

  InitialOuter : List Elt → Int → Set
  InitialOuter original n =
    (oneZ ≤Z oneZ) ∧
    Perm original original ∧
    BlocksSorted original oneZ zeroZ n n

  OuterInvariant :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  OuterInvariant original current n runLength =
    (oneZ ≤Z runLength) ∧
    Perm original current ∧
    BlocksSorted current runLength zeroZ n n

  InitialInner : List Elt → Int → Int → Set
  InitialInner current n runLength =
    ((zeroZ ≤Z zeroZ) ∧
     (zeroZ ≡ multiplyInt (multiplyInt twoZ zeroZ) runLength)) ∧
    Perm current current ∧
    BlocksSorted current runLength zeroZ n n ∧
    BlocksSorted
      current
      (multiplyInt twoZ runLength)
      zeroZ
      zeroZ
      n

  InnerInvariant :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  InnerInvariant before current n runLength i =
    let base = multiplyInt (multiplyInt twoZ i) runLength
    in
    (zeroZ ≤Z base) ∧
    Perm before current ∧
    BlocksSorted current runLength base n n ∧
    BlocksSorted
      current
      (multiplyInt twoZ runLength)
      zeroZ
      base
      n

  MergeBounds :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  MergeBounds temporary current base middle high =
    ((zeroZ ≤Z base) ∧
     (base ≤Z middle) ∧
     (middle ≤Z high) ∧
     (high ≤Z lengthZ temporary) ∧
     (length temporary ≡ length current)) ∧
    sortedSub current base middle ∧
    sortedSub current middle high

  OutsideMergeEqual :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  OutsideMergeEqual before after base high =
    (index : Int) →
    (((zeroZ ≤Z index) ∧ (index <Z base)) ∨
     ((high ≤Z index) ∧ (index <Z lengthZ after))) →
    nthElt after index ≡ nthElt before index

  MergeResultPremise :
    List Elt →
    Int →
    Int →
    List Elt →
    Set
  MergeResultPremise before base high result =
    sortedSub result base high ∧
    permutSub before result (toNat base) (toNat high) ∧
    OutsideMergeEqual before result base high

  MergeResultConclusion :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Int →
    Int →
    List Elt →
    Set
  MergeResultConclusion original outerStart n runLength i middle high result =
    let base = multiplyInt (multiplyInt twoZ i) runLength
        nextBoundary = addInt middle runLength
    in
    ((zeroZ ≤Z
        (subtractInt
          (addInt n runLength)
          base)) ∧
     (subtractInt
        (addInt n runLength)
        nextBoundary
      <Z
      subtractInt
        (addInt n runLength)
        base)) ∧
    ((zeroZ ≤Z nextBoundary) ∧
     (nextBoundary ≡
      multiplyInt
        (multiplyInt twoZ (addInt i oneZ))
        runLength)) ∧
    Perm outerStart result ∧
    BlocksSorted result runLength nextBoundary n n ∧
    BlocksSorted
      result
      (multiplyInt twoZ runLength)
      zeroZ
      nextBoundary
      n

  MergeCase :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    List Elt →
    Set
  MergeCase original outerStart current n runLength i temporary =
    let base = multiplyInt (multiplyInt twoZ i) runLength
        middle = addInt base runLength
        high = minInt n (addInt middle runLength)
    in
    MergeBounds temporary current base middle high ∧
    ((result : List Elt) →
      (length result ≡ length current) →
      MergeResultPremise current base high result →
      MergeResultConclusion
        original
        outerStart
        n
        runLength
        i
        middle
        high
        result)

  InnerFinish :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  InnerFinish original current n runLength =
    ((zeroZ ≤Z
       subtractInt (multiplyInt twoZ n) runLength) ∧
     (subtractInt
       (multiplyInt twoZ n)
       (multiplyInt twoZ runLength)
      <Z
      subtractInt (multiplyInt twoZ n) runLength)) ∧
    (oneZ ≤Z multiplyInt twoZ runLength) ∧
    Perm original current ∧
    BlocksSorted
      current
      (multiplyInt twoZ runLength)
      zeroZ
      n
      n

  InnerStep :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    List Elt →
    Set
  InnerStep original outerStart current n runLength i temporary =
    let base = multiplyInt (multiplyInt twoZ i) runLength
    in
    IfSet
      (intLess base (subtractInt n runLength))
      (MergeCase
        original
        outerStart
        current
        n
        runLength
        i
        temporary)
      (InnerFinish original current n runLength)

  InnerLoop :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  InnerLoop original outerStart temporary n runLength =
    (i : Int) →
    (temporary₂ : List Elt) →
    (current : List Elt) →
    (length temporary₂ ≡ length temporary) →
    (length current ≡ length outerStart) →
    InnerInvariant outerStart current n runLength i →
    InnerStep
      original
      outerStart
      current
      n
      runLength
      i
      temporary₂

  OuterStep :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  OuterStep original temporary current n runLength =
    IfSet
      (intLess runLength n)
      (InitialInner current n runLength ∧
       InnerLoop original current temporary n runLength)
      (sorted current ∧ Perm original current)

  BottomUpMergesortVC : List Elt → Set
  BottomUpMergesortVC original =
    let n = lengthZ original
    in
    (temporary : List Elt) →
    ((length temporary ≡ length original) ∧
     ((index : Int) →
      ((zeroZ ≤Z index) ∧ (index <Z lengthZ temporary)) →
      nthElt temporary index ≡ nthElt original index)) →
    InitialOuter original n ∧
    ((runLength : Int) →
      (temporary₁ : List Elt) →
      (current : List Elt) →
      (length temporary₁ ≡ length temporary) →
      (length current ≡ length original) →
      OuterInvariant original current n runLength →
      OuterStep
        original
        temporary₁
        current
        n
        runLength)

  bottom-up-mergesort'vc : Set
  bottom-up-mergesort'vc =
    (original : List Elt) →
    BottomUpMergesortVC original
