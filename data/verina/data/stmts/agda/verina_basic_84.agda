-- Statement-only formalization of VERINA corpus artifact verina_basic_84,
-- catalog title "replace": a deterministic integer-array scan replaces every
-- element strictly greater than the threshold with -1, leaves every other
-- element unchanged, and is connected to its correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic84 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero n = true
natLessOrEqual (suc m) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos m) (negsuc n) = false
intLess (negsuc m) (pos n) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos m) (negsuc n) = false
intLessOrEqual (negsuc m) (pos n) = true
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

zeroInt : Int
zeroInt = pos zero

minusOne : Int
minusOne = negsuc zero

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

updateAt : {A : Set} → Array A → Nat → A → Array A
updateAt [] index value = []
updateAt (x ∷ xs) zero value = value ∷ xs
updateAt (x ∷ xs) (suc index) value =
  x ∷ updateAt xs index value

dropArray : {A : Set} → Nat → Array A → Array A
dropArray zero xs = xs
dropArray (suc n) [] = []
dropArray (suc n) (_ ∷ xs) = dropArray n xs

replace-precond : Array Int → Int → Set
replace-precond arr k = Top

replace-loop-tail :
  Int →
  Array Int →
  Nat →
  Array Int →
  Array Int
replace-loop-tail k [] i accumulator = accumulator
replace-loop-tail k (x ∷ xs) i accumulator =
  let next =
        if intLess k x
        then updateAt accumulator i minusOne
        else accumulator
  in replace-loop-tail k xs (suc i) next

-- Dropping i elements exposes exactly the suffix visited by the source loop
-- from index i; each step performs the same conditional in-place update.
replace-loop :
  Array Int →
  Int →
  Nat →
  Array Int →
  Array Int
replace-loop oldArr k i accumulator =
  replace-loop-tail k (dropArray i oldArr) i accumulator

replace :
  (arr : Array Int) →
  (k : Int) →
  replace-precond arr k →
  Array Int
replace arr k h-precond =
  replace-loop arr k zero arr

replace-postcond :
  (arr : Array Int) →
  (k : Int) →
  (result : Array Int) →
  replace-precond arr k →
  Set
replace-postcond arr k result h-precond =
  (arraySize result ≡ arraySize arr) ∧
  ((i : Nat) →
    i < arraySize arr →
    IsTrue (intLess k (indexDefault zeroInt arr i)) →
    indexDefault zeroInt result i ≡ minusOne) ∧
  ((i : Nat) →
    i < arraySize arr →
    IsTrue (intLessOrEqual (indexDefault zeroInt arr i) k) →
    indexDefault zeroInt result i ≡
      indexDefault zeroInt arr i)

replace-spec-satisfied : Set
replace-spec-satisfied =
  (arr : Array Int) →
  (k : Int) →
  (h-precond : replace-precond arr k) →
  replace-postcond
    arr
    k
    (replace arr k h-precond)
    h-precond
