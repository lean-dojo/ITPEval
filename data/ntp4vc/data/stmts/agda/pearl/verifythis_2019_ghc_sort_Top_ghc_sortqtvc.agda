-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2019_ghc_sort_Top_ghc_sortqtvc: the GHC-sort verification
-- condition carrying sorted-list and occurrence information through copying
-- back into an integer array, yielding sortedness and permutation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2019GhcSortTopGhcSortVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = pos (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

countList : Int → List Int → Nat
countList value [] = zero
countList value (x ∷ xs) with intEqual value x
... | true = suc (countList value xs)
... | false = countList value xs

mapOccFrom : Int → List Int → Int → Nat → Nat
mapOccFrom value xs index zero = zero
mapOccFrom value xs index (suc remaining) with
  intEqual (nthInt xs index) value
... | true =
  suc (mapOccFrom value xs (addInt index oneZ) remaining)
... | false =
  mapOccFrom value xs (addInt index oneZ) remaining

mapOcc : Int → List Int → Int → Int → Nat
mapOcc value xs lower upper =
  mapOccFrom
    value
    xs
    lower
    (toNat (subtractInt upper lower))

data SortedList : List Int → Set where
  sortedNil :
    SortedList []

  sortedOne :
    (x : Int) →
    SortedList (x ∷ [])

  sortedTwo :
    (x y : Int) →
    (tail : List Int) →
    x ≤Z y →
    SortedList (y ∷ tail) →
    SortedList (x ∷ y ∷ tail)

ArraySorted : List Int → Set
ArraySorted xs =
  (i j : Int) →
  ((zeroZ ≤Z i) ∧ (i ≤Z j) ∧ (j <Z lengthZ xs)) →
  nthInt xs i ≤Z nthInt xs j

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

OccurrencesMatch : List Int → List Int → Set
OccurrencesMatch arrayValues listValues =
  (value : Int) →
  mapOcc value arrayValues zeroZ (lengthZ arrayValues) ≡
    countList value listValues

CopiedFrom : List Int → List Int → Set
CopiedFrom destination source =
  (index : Int) →
  ((zeroZ ≤Z index) ∧ (index <Z lengthZ destination)) →
  nthInt destination index ≡
    nthInt source (subtractInt index zeroZ)

PrefixPreserved : List Int → List Int → Set
PrefixPreserved destination original =
  (index : Int) →
  ((zeroZ ≤Z index) ∧ (index <Z zeroZ)) →
  nthInt destination index ≡ nthInt original index

CopyBackConclusion : List Int → List Int → Set
CopyBackConclusion original sortedValues =
  ((zeroZ ≤Z zeroZ) ∧
   (lengthZ sortedValues ≡
    subtractInt (lengthZ original) zeroZ))
  ∧
  ((destination : List Int) →
    length destination ≡ length original →
    (CopiedFrom destination sortedValues
     ∧ PrefixPreserved destination original
     ∧ OccurrencesMatch destination sortedValues) →
    ArraySorted destination ∧ Perm destination original)

NonemptyBranch : List Int → Set
NonemptyBranch original =
  (zeroZ <Z lengthZ original)
  ∧
  ((sortedValues : List Int) →
    (SortedList sortedValues
     ∧ OccurrencesMatch original sortedValues
     ∧ (length sortedValues ≡ length original)) →
    CopyBackConclusion original sortedValues)

GhcSortGoal : List Int → Set
GhcSortGoal original =
  IfSet
    (natEqual (length original) zero)
    (ArraySorted original ∧ Perm original original)
    (NonemptyBranch original)

ghc-sort'vc : Set
ghc-sort'vc =
  (original : List Int) →
  GhcSortGoal original
