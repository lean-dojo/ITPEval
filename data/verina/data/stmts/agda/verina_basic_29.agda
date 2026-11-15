-- Statement-only formalization of VERINA corpus artifact verina_basic_29,
-- catalog title "removeElement": a deterministic integer-array program removes
-- the element at a valid index and is connected to its length, unchanged-prefix,
-- and shifted-suffix correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic29 where

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

eraseAt : {A : Set} → Nat → Array A → Array A
eraseAt zero [] = []
eraseAt zero (_ ∷ xs) = xs
eraseAt (suc index) [] = []
eraseAt (suc index) (x ∷ xs) =
  x ∷ eraseAt index xs

zeroInt : Int
zeroInt = pos zero

one : Nat
one = suc zero

removeElement-precond : Array Int → Nat → Set
removeElement-precond s k =
  k < arraySize s

removeElement :
  (s : Array Int) →
  (k : Nat) →
  removeElement-precond s k →
  Array Int
removeElement s k h-precond =
  eraseAt k s

removeElement-postcond :
  (s : Array Int) →
  (k : Nat) →
  (result : Array Int) →
  removeElement-precond s k →
  Set
removeElement-postcond s k result h-precond =
  (arraySize result ≡ natSubtract (arraySize s) one) ∧
  ((i : Nat) →
    i < k →
    indexDefault zeroInt result i ≡
      indexDefault zeroInt s i) ∧
  ((i : Nat) →
    i < arraySize result →
    k ≤ i →
    indexDefault zeroInt result i ≡
      indexDefault zeroInt s (i + one))

removeElement-spec-satisfied : Set
removeElement-spec-satisfied =
  (s : Array Int) →
  (k : Nat) →
  (h-precond : removeElement-precond s k) →
  removeElement-postcond
    s
    k
    (removeElement s k h-precond)
    h-precond
