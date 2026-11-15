-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/sumrange_CumulativeArray_queryqtvc: a cumulative-sum array query
-- returns the integer sum over the requested half-open index range while
-- preserving the query's array-index bounds. This file contains no proof.

{-# OPTIONS --safe #-}

module sumrange_CumulativeArray_queryqtvc where

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

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : List Int → Int → Int
nthInt xs index = nthDefault zeroZ (toNat index) xs

sumFrom : List Int → Nat → Nat → Int
sumFrom values start zero = zeroZ
sumFrom values start (suc count) =
  addInt
    (nthDefault zeroZ start values)
    (sumFrom values (suc start) count)

sumRange : List Int → Int → Int → Int
sumRange values lower upper =
  sumFrom
    values
    (toNat lower)
    (toNat (subtractInt upper lower))

IsCumulativeArrayFor :
  List Int →
  List Int →
  Set
IsCumulativeArrayFor cumulative source =
  (lengthZ cumulative ≡ addInt (lengthZ source) oneZ) ∧
  ((index : Int) →
    ((zeroZ ≤Z index) ∧ (index <Z lengthZ cumulative)) →
    nthInt cumulative index ≡ sumRange source zeroZ index)

query'vc : Set
query'vc =
  (cumulative source : List Int) →
  (i j : Int) →
  IsCumulativeArrayFor cumulative source →
  zeroZ ≤Z i →
  i ≤Z j →
  j <Z lengthZ cumulative →
  (zeroZ ≤Z i) ∧
  (i <Z lengthZ cumulative) ∧
  (zeroZ ≤Z j) ∧
  (j <Z lengthZ cumulative) ∧
  (subtractInt (nthInt cumulative j) (nthInt cumulative i)
    ≡ sumRange source i j)
