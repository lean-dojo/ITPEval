-- Statement-only formalization of VERINA corpus artifact verina_basic_28,
-- catalog title "isPrime": a deterministic fuel-bounded divisor scan decides
-- primality for natural numbers at least two and is connected to its full
-- divisibility correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic28 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infixr 3 _∧_
infix 4 _≤_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

two : Nat
two = suc (suc zero)

isPrime-precond : Nat → Set
isPrime-precond n = two ≤ n

isPrime-check : Nat → Nat → Nat → Bool
isPrime-check n i zero = true
isPrime-check n i (suc fuel) =
  if natLess n (i * i)
  then true
  else
    if natEqual (naturalMod n i) zero
    then false
    else isPrime-check n (suc i) fuel

isPrime :
  (n : Nat) →
  isPrime-precond n →
  Bool
isPrime n h-precond =
  isPrime-check n two n

isPrime-postcond :
  (n : Nat) →
  (result : Bool) →
  isPrime-precond n →
  Set
isPrime-postcond n result h-precond =
  let candidates = rangeFrom two (natSubtract n two)
  in
    (IsTrue result →
      IsTrue
        (allList
          (λ k → notBool (natEqual (naturalMod n k) zero))
          candidates)) ∧
    (Not (IsTrue result) →
      IsTrue
        (anyList
          (λ k → natEqual (naturalMod n k) zero)
          candidates))

isPrime-spec-satisfied : Set
isPrime-spec-satisfied =
  (n : Nat) →
  (h-precond : isPrime-precond n) →
  isPrime-postcond
    n
    (isPrime n h-precond)
    h-precond
