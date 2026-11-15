-- Statement-only formalization of VERINA corpus artifact verina_advanced_36,
-- catalog title "majorityElement": the Boyer-Moore candidate-selection program
-- returns a natural number occurring strictly more than half the time in a
-- nonempty list that has a majority element. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced36 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
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

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

countNat : Nat → List Nat → Nat
countNat sought [] = zero
countNat sought (x ∷ xs) =
  if natEqual sought x
  then suc (countNat sought xs)
  else countNat sought xs

anyMajority : List Nat → List Nat → Bool
anyMajority original [] = false
anyMajority original (x ∷ xs) =
  if natLess (half (listLength original)) (countNat x original)
  then true
  else anyMajority original xs

record majorityElement-precond (xs : List Nat) : Set where
  constructor precondition
  field
    nonempty : zero < listLength xs
    majority-exists : IsTrue (anyMajority xs xs)

countOccurrences : Nat → List Nat → Nat
countOccurrences target [] = zero
countOccurrences target (y ∷ ys) =
  if natEqual y target
  then suc (countOccurrences target ys)
  else countOccurrences target ys

findCandidate : List Nat → Maybe Nat → Nat → Nat
findCandidate [] (just candidate) count = candidate
findCandidate [] nothing count = zero
findCandidate (x ∷ xs) (just candidate) count =
  if natEqual x candidate
  then findCandidate xs (just candidate) (count + suc zero)
  else
    if natEqual count zero
    then findCandidate xs (just x) (suc zero)
    else findCandidate xs (just candidate) (predecessor count)
findCandidate (x ∷ xs) nothing count =
  findCandidate xs (just x) (suc zero)

majorityElement :
  (xs : List Nat) →
  majorityElement-precond xs →
  Nat
majorityElement xs h-precond =
  findCandidate xs nothing zero

majorityElement-postcond :
  (xs : List Nat) →
  (result : Nat) →
  majorityElement-precond xs →
  Set
majorityElement-postcond xs result h-precond =
  half (listLength xs) < countNat result xs

majorityElement-spec-satisfied : Set
majorityElement-spec-satisfied =
  (xs : List Nat) →
  (h-precond : majorityElement-precond xs) →
  majorityElement-postcond
    xs
    (majorityElement xs h-precond)
    h-precond
