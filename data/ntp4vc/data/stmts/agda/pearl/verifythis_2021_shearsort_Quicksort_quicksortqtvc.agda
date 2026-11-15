-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2021_shearsort_Quicksort_quicksortqtvc: the whole-array
-- quicksort verification condition, transferring full-range sortedness and
-- permutation guarantees to the global postcondition. This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2021ShearsortQuicksortQuicksortQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ : Int
zeroZ = pos zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

take : {A : Set} → Nat → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

slice : {A : Set} → List A → Nat → Nat → List A
slice xs lower upper =
  take (natSubtract upper lower) (drop lower xs)

data Permutation {A : Set} : List A → List A → Set where
  permutationNil :
    Permutation [] []

  permutationSkip :
    {x : A} {xs ys : List A} →
    Permutation xs ys →
    Permutation (x ∷ xs) (x ∷ ys)

  permutationSwap :
    {x y : A} {xs : List A} →
    Permutation (y ∷ x ∷ xs) (x ∷ y ∷ xs)

  permutationTrans :
    {xs ys zs : List A} →
    Permutation xs ys →
    Permutation ys zs →
    Permutation xs zs

PermutSub : List Int → List Int → Nat → Nat → Set
PermutSub a1 a2 lower upper =
  (length a1 ≡ length a2) ∧
  (slice a1 zero lower ≡ slice a2 zero lower) ∧
  (slice a1 upper (length a1) ≡
    slice a2 upper (length a1)) ∧
  Permutation
    (slice a1 lower upper)
    (slice a2 lower upper)

SortedSub : List Int → Int → Int → Set
SortedSub xs lower upper =
  (i1 i2 : Int) →
  (lower ≤Z i1 ∧ i1 ≤Z i2 ∧ i2 <Z upper) →
  nthInt xs i1 ≤Z nthInt xs i2

Sorted : List Int → Set
Sorted xs = SortedSub xs zeroZ (lengthZ xs)

QSPartition :
  List Int → List Int →
  Int → Int → Int → Int → Set
QSPartition a1 a2 lower middle upper pivot =
  PermutSub a1 a2 (toNat lower) (toNat upper) ∧
  ((j : Int) →
    (lower ≤Z j ∧ j <Z middle) →
    nthInt a2 j <Z pivot) ∧
  ((j : Int) →
    (middle <Z j ∧ j <Z upper) →
    pivot ≤Z nthInt a2 j) ∧
  nthInt a2 middle ≡ pivot

QuicksortVC : List Int → Set
QuicksortVC a =
  let o1 = lengthZ a
  in
  (zeroZ ≤Z zeroZ ∧
    zeroZ ≤Z o1 ∧
    o1 ≤Z lengthZ a) ∧
  ((a1 : List Int) →
    (length a1 ≡ length a) →
    (SortedSub a1 zeroZ o1 ∧
      PermutSub a a1 zero (toNat o1)) →
    Sorted a1 ∧ Permutation a a1)

quicksort'vc : Set
quicksort'vc =
  (a : List Int) →
  QuicksortVC a
