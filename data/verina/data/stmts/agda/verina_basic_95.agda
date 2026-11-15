-- Statement-only formalization of VERINA corpus artifact verina_basic_95,
-- catalog title "swap": a deterministic integer-array program exchanges the
-- entries at two nonnegative in-bounds integer indices, preserves every other
-- entry and the array size, and is connected to its correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic95 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_ _≢_

data Bottom : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → Bottom

data IntNonnegative : Int → Set where
  nonnegative : {n : Nat} → IntNonnegative (pos n)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

zeroInt : Int
zeroInt = pos zero

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

swap-precond : Array Int → Int → Int → Set
swap-precond arr i j =
  IntNonnegative i ∧
  IntNonnegative j ∧
  intToNat i < arraySize arr ∧
  intToNat j < arraySize arr

swap :
  (arr : Array Int) →
  (i j : Int) →
  swap-precond arr i j →
  Array Int
swap arr i j h-precond =
  let i-nat = intToNat i
      j-nat = intToNat j
      arr1 =
        updateAt arr i-nat
          (indexDefault zeroInt arr j-nat)
      arr2 =
        updateAt arr1 j-nat
          (indexDefault zeroInt arr i-nat)
  in arr2

swap-postcond :
  (arr : Array Int) →
  (i j : Int) →
  (result : Array Int) →
  swap-precond arr i j →
  Set
swap-postcond arr i j result h-precond =
  (arraySize result ≡ arraySize arr) ∧
  (indexDefault zeroInt result (intToNat i) ≡
    indexDefault zeroInt arr (intToNat j)) ∧
  (indexDefault zeroInt result (intToNat j) ≡
    indexDefault zeroInt arr (intToNat i)) ∧
  ((k : Nat) →
    k < arraySize arr →
    k ≢ intToNat i →
    k ≢ intToNat j →
    indexDefault zeroInt result k ≡
      indexDefault zeroInt arr k)

swap-spec-satisfied : Set
swap-spec-satisfied =
  (arr : Array Int) →
  (i j : Int) →
  (h-precond : swap-precond arr i j) →
  swap-postcond
    arr
    i
    j
    (swap arr i j h-precond)
    h-precond
