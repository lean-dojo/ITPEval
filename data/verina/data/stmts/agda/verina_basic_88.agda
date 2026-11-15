-- Statement-only formalization of VERINA corpus artifact verina_basic_88,
-- catalog title "ToArray": the deterministic conversion of an integer list
-- to an array preserves its length and every element at each valid index.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic88 where

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

zeroInt : Int
zeroInt = pos zero

Array : Set → Set
Array A = List A

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

listToArray : {A : Set} → List A → Array A
listToArray [] = []
listToArray (x ∷ xs) = x ∷ listToArray xs

ToArray-precond : List Int → Set
ToArray-precond xs = Top

ToArray :
  (xs : List Int) →
  ToArray-precond xs →
  Array Int
ToArray xs h-precond =
  listToArray xs

ToArray-postcond :
  (xs : List Int) →
  (result : Array Int) →
  ToArray-precond xs →
  Set
ToArray-postcond xs result h-precond =
  (arraySize result ≡ listLength xs) ∧
  ((i : Nat) →
    i < listLength xs →
    indexDefault zeroInt result i ≡
      indexDefault zeroInt xs i)

ToArray-spec-satisfied : Set
ToArray-spec-satisfied =
  (xs : List Int) →
  (h-precond : ToArray-precond xs) →
  ToArray-postcond
    xs
    (ToArray xs h-precond)
    h-precond
