-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/mergesort_array_TopDownMergesort_mergesort_recqtvc: the top-down
-- mergesort recursive verification condition for sorted subarrays,
-- subarray permutations, and the two recursive and merge continuations.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module mergesort_array_TopDownMergesort_mergesort_recqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤N_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

-- Signed division by two truncated toward zero, matching Int.tdiv and cdiv.
tdivTwo : Int → Int
tdivTwo (pos n) = pos (halfNat n)
tdivTwo (negsuc n) = negative (halfNat (suc n))

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

permutSubPrime : {A : Set} → List A → List A → Nat → Nat → Set
permutSubPrime xs ys lower upper =
  (length xs ≡ length ys) ∧
  (slice xs zero lower ≡ slice ys zero lower) ∧
  (slice xs upper (length xs) ≡ slice ys upper (length xs)) ∧
  Perm (slice xs lower upper) (slice ys lower upper)

module TopDownMergesortTheory
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

  unchangedOutside :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  unchangedOutside current previous lower upper =
    (index : Int) →
    (((zeroZ ≤Z index) ∧ (index <Z lower)) ∨
     ((upper ≤Z index) ∧ (index <Z lengthZ current))) →
    nthElt current index ≡ nthElt previous index

  AllMergedResults :
    List Elt →
    List Elt →
    Int →
    Int →
    Set
  AllMergedResults original a₂ lower upper =
    (a₃ : List Elt) →
    (length a₃ ≡ length a₂) →
    (sortedSub a₃ lower upper ∧
     permutSub a₂ a₃ (toNat lower) (toNat upper) ∧
     unchangedOutside a₃ a₂ lower upper) →
    sortedSub a₃ lower upper ∧
    permutSubPrime original a₃ (toNat lower) (toNat upper)

  MergeObligations :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  MergeObligations original a₂ tmp₂ lower middle upper =
    (((zeroZ ≤Z lower) ∧
      (lower ≤Z middle) ∧
      (middle ≤Z upper) ∧
      (upper ≤Z lengthZ tmp₂) ∧
      (length tmp₂ ≡ length a₂)) ∧
     sortedSub a₂ lower middle ∧
     sortedSub a₂ middle upper) ∧
    AllMergedResults original a₂ lower upper

  AllSecondResults :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  AllSecondResults original a₁ tmp₁ lower middle upper =
    (tmp₂ a₂ : List Elt) →
    (length tmp₂ ≡ length tmp₁) →
    (length a₂ ≡ length a₁) →
    (sortedSub a₂ middle upper ∧
     permutSubPrime a₁ a₂ (toNat middle) (toNat upper)) →
    MergeObligations original a₂ tmp₂ lower middle upper

  SecondRecursionConclusion :
    List Elt →
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  SecondRecursionConclusion original a₁ tmp₁ lower middle upper =
    (((zeroZ ≤Z subtractInt upper lower) ∧
      (subtractInt upper middle <Z subtractInt upper lower)) ∧
     (zeroZ ≤Z middle) ∧
     (middle ≤Z upper) ∧
     (upper ≤Z lengthZ a₁) ∧
     (length a₁ ≡ length tmp₁)) ∧
    AllSecondResults original a₁ tmp₁ lower middle upper

  AllFirstResults :
    List Elt →
    List Elt →
    Int →
    Int →
    Int →
    Set
  AllFirstResults original tmp lower middle upper =
    (tmp₁ a₁ : List Elt) →
    (length tmp₁ ≡ length tmp) →
    (length a₁ ≡ length original) →
    (sortedSub a₁ lower middle ∧
     permutSubPrime original a₁ (toNat lower) (toNat middle)) →
    SecondRecursionConclusion
      original a₁ tmp₁ lower middle upper

  RecursiveBranch :
    Int →
    Int →
    List Elt →
    List Elt →
    Set
  RecursiveBranch lower upper original tmp =
    Not (twoZ ≡ zeroZ) ∧
    let middle =
          addInt lower (tdivTwo (subtractInt upper lower))
    in
    (((zeroZ ≤Z subtractInt upper lower) ∧
      (subtractInt middle lower <Z subtractInt upper lower)) ∧
     (zeroZ ≤Z lower) ∧
     (lower ≤Z middle) ∧
     (middle ≤Z lengthZ original) ∧
     (length original ≡ length tmp)) ∧
    AllFirstResults original tmp lower middle upper

  BaseBranch :
    Int →
    Int →
    List Elt →
    Set
  BaseBranch lower upper original =
    sortedSub original lower upper ∧
    permutSubPrime
      original
      original
      (toNat lower)
      (toNat upper)

  MergesortRecVC :
    Int →
    Int →
    List Elt →
    List Elt →
    Set
  MergesortRecVC lower upper original tmp =
    (zeroZ ≤Z lower) →
    (lower ≤Z upper) →
    (upper ≤Z lengthZ original) →
    (length original ≡ length tmp) →
    IfSet
      (intLessOrEqual (subtractInt upper oneZ) lower)
      (BaseBranch lower upper original)
      (RecursiveBranch lower upper original tmp)

  mergesort-rec'vc : Set
  mergesort-rec'vc =
    (lower upper : Int) →
    (original tmp : List Elt) →
    MergesortRecVC lower upper original tmp
