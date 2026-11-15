-- Statement-only formalization of VERINA corpus artifact verina_basic_85,
-- catalog title "reverse": a deterministic integer-array program swaps
-- mirrored pairs to reverse the array and is connected to its size-and-index
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic85 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos)
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

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

one : Nat
one = suc zero

zeroInt : Int
zeroInt = pos zero

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

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

reverse-precond : Array Int → Set
reverse-precond a = Top

reverse-core-fuel :
  Array Int →
  Nat →
  Nat →
  Array Int
reverse-core-fuel arr i zero = arr
reverse-core-fuel arr i (suc remaining) =
  let j = natSubtract (natSubtract (arraySize arr) one) i
      temp = indexDefault zeroInt arr i
      arr′ = updateAt arr i (indexDefault zeroInt arr j)
      arr″ = updateAt arr′ j temp
  in reverse-core-fuel arr″ (suc i) remaining

-- Each swap preserves size, so floor(size / 2) - i is exactly the number of
-- iterations for which the source helper's guard i < size / 2 remains true.
reverse-core : Array Int → Nat → Array Int
reverse-core arr i =
  reverse-core-fuel
    arr
    i
    (natSubtract (half (arraySize arr)) i)

reverse :
  (a : Array Int) →
  reverse-precond a →
  Array Int
reverse a h-precond =
  reverse-core a zero

reverse-postcond :
  (a : Array Int) →
  (result : Array Int) →
  reverse-precond a →
  Set
reverse-postcond a result h-precond =
  (arraySize result ≡ arraySize a) ∧
  ((i : Nat) →
    i < arraySize a →
    indexDefault zeroInt result i ≡
    indexDefault
      zeroInt
      a
      (natSubtract (natSubtract (arraySize a) one) i))

reverse-spec-satisfied : Set
reverse-spec-satisfied =
  (a : Array Int) →
  (h-precond : reverse-precond a) →
  reverse-postcond
    a
    (reverse a h-precond)
    h-precond
