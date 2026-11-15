-- Statement-only formalization of VERINA corpus artifact verina_basic_97,
-- catalog title "TestArrayElements": a deterministic integer-array program
-- sets the element at an in-bounds natural index to 60, preserves the array
-- size and every other element, and is connected to its correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic97 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos)
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

zeroInt : Int
zeroInt = pos zero

sixty : Int
sixty = pos 60

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

TestArrayElements-precond : Array Int → Nat → Set
TestArrayElements-precond a j =
  j < arraySize a

TestArrayElements :
  (a : Array Int) →
  (j : Nat) →
  TestArrayElements-precond a j →
  Array Int
TestArrayElements a j h-precond =
  updateAt a j sixty

TestArrayElements-postcond :
  (a : Array Int) →
  (j : Nat) →
  (result : Array Int) →
  TestArrayElements-precond a j →
  Set
TestArrayElements-postcond a j result h-precond =
  (arraySize result ≡ arraySize a) ∧
  (indexDefault zeroInt result j ≡ sixty) ∧
  ((k : Nat) →
    k < arraySize a →
    k ≢ j →
    indexDefault zeroInt result k ≡
      indexDefault zeroInt a k)

TestArrayElements-spec-satisfied : Set
TestArrayElements-spec-satisfied =
  (a : Array Int) →
  (j : Nat) →
  (h-precond : TestArrayElements-precond a j) →
  TestArrayElements-postcond
    a
    j
    (TestArrayElements a j h-precond)
    h-precond
