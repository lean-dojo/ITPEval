-- Statement-only formalization of VERINA corpus artifact verina_basic_32,
-- catalog title "swapFirstAndLast": a deterministic integer-array program
-- swaps the first and last elements of a nonempty array, preserves its size
-- and interior elements, and is connected to its correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic32 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infix 4 _≤_ _<_

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

zeroInt : Int
zeroInt = pos zero

one : Nat
one = suc zero

two : Nat
two = suc one

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

swapFirstAndLast-precond : Array Int → Set
swapFirstAndLast-precond a =
  zero < arraySize a

swapFirstAndLast :
  (a : Array Int) →
  swapFirstAndLast-precond a →
  Array Int
swapFirstAndLast a h-precond =
  let first = indexDefault zeroInt a zero
      last-index = natSubtract (arraySize a) one
      last = indexDefault zeroInt a last-index
      first-updated = updateAt a zero last
  in updateAt first-updated last-index first

swapFirstAndLast-postcond :
  (a : Array Int) →
  (result : Array Int) →
  swapFirstAndLast-precond a →
  Set
swapFirstAndLast-postcond a result h-precond =
  (arraySize result ≡ arraySize a) ∧
  (indexDefault zeroInt result zero ≡
    indexDefault zeroInt a (natSubtract (arraySize a) one)) ∧
  (indexDefault zeroInt result
      (natSubtract (arraySize result) one) ≡
    indexDefault zeroInt a zero) ∧
  ((i : Nat) →
    i < natSubtract (arraySize result) two →
    indexDefault zeroInt result (i + one) ≡
      indexDefault zeroInt a (i + one))

swapFirstAndLast-spec-satisfied : Set
swapFirstAndLast-spec-satisfied =
  (a : Array Int) →
  (h-precond : swapFirstAndLast-precond a) →
  swapFirstAndLast-postcond
    a
    (swapFirstAndLast a h-precond)
    h-precond
