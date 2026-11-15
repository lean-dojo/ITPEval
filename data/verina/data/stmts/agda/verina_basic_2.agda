-- Statement-only formalization of VERINA corpus artifact verina_basic_2,
-- catalog title "findSmallest": a deterministic natural-number array minimum
-- returns none exactly for an empty array and otherwise returns an element no
-- greater than any array element. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _∈_

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

data _∈_ (x : Nat) : List Nat → Set where
  here : {xs : List Nat} → x ∈ (x ∷ xs)
  there : {y : Nat} {xs : List Nat} → x ∈ xs → x ∈ (y ∷ xs)

Array : Set → Set
Array A = List A

natMin : Nat → Nat → Nat
natMin zero n = zero
natMin (suc m) zero = zero
natMin (suc m) (suc n) = suc (natMin m n)

listMinMaybe : List Nat → Maybe Nat
listMinMaybe [] = nothing
listMinMaybe (x ∷ xs) with listMinMaybe xs
... | nothing = just x
... | just y = just (natMin x y)

findSmallest-precond : Array Nat → Set
findSmallest-precond s = Top

findSmallest :
  (s : Array Nat) →
  findSmallest-precond s →
  Maybe Nat
findSmallest s h-precond =
  listMinMaybe s

findSmallest-postcond :
  (s : Array Nat) →
  (result : Maybe Nat) →
  findSmallest-precond s →
  Set
findSmallest-postcond s nothing h-precond =
  s ≡ []
findSmallest-postcond s (just r) h-precond =
  (r ∈ s) ∧
  ((x : Nat) → x ∈ s → r ≤ x)

findSmallest-spec-satisfied : Set
findSmallest-spec-satisfied =
  (s : Array Nat) →
  (h-precond : findSmallest-precond s) →
  findSmallest-postcond
    s
    (findSmallest s h-precond)
    h-precond
