-- Statement-only formalization of VERINA corpus artifact verina_basic_94,
-- catalog title "iter_copy": a deterministic integer-array loop copies every
-- element in order into a fresh result and is connected to its size-and-index
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic94 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_ _<_
infixr 3 _∧_

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

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexMaybe : {A : Set} → Array A → Nat → Maybe A
indexMaybe [] index = nothing
indexMaybe (x ∷ xs) zero = just x
indexMaybe (x ∷ xs) (suc index) = indexMaybe xs index

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

push : {A : Set} → Array A → A → Array A
push [] value = value ∷ []
push (x ∷ xs) value = x ∷ push xs value

iter-copy-precond : Array Int → Set
iter-copy-precond s = Top

iter-copy-loop :
  Array Int →
  Nat →
  Nat →
  Array Int →
  Array Int
iter-copy-loop s zero i accumulator = accumulator
iter-copy-loop s (suc remaining) i accumulator with indexMaybe s i
... | just value =
  iter-copy-loop s remaining (suc i) (push accumulator value)
... | nothing = accumulator

iter-copy :
  (s : Array Int) →
  iter-copy-precond s →
  Array Int
iter-copy s h-precond =
  iter-copy-loop s (arraySize s) zero []

iter-copy-postcond :
  (s : Array Int) →
  (result : Array Int) →
  iter-copy-precond s →
  Set
iter-copy-postcond s result h-precond =
  (arraySize s ≡ arraySize result) ∧
  ((i : Nat) →
    i < arraySize s →
    indexDefault zeroInt s i ≡
      indexDefault zeroInt result i)

iter-copy-spec-satisfied : Set
iter-copy-spec-satisfied =
  (s : Array Int) →
  (h-precond : iter-copy-precond s) →
  iter-copy-postcond
    s
    (iter-copy s h-precond)
    h-precond
