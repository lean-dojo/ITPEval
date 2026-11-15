-- Statement-only formalization of VERINA corpus artifact verina_advanced_9,
-- catalog title "countSumDivisibleBy": a deterministic program counts the
-- naturals below a bound whose decimal digit sum is divisible by a positive
-- divisor, and is connected to its filtered-count contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced9 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; div-helper; mod-helper)

infixr 3 _∧_
infix 4 _≤_ _<_
infixr 5 _&&_

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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

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

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

ten : Nat
ten =
  suc
    (suc
      (suc
        (suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc zero)))))))))

sumOfDigitsWithFuel : Nat → Nat → Nat → Nat
sumOfDigitsWithFuel zero current accumulator = accumulator
sumOfDigitsWithFuel (suc fuel) zero accumulator = accumulator
sumOfDigitsWithFuel (suc fuel) (suc current) accumulator =
  sumOfDigitsWithFuel
    fuel
    (naturalDiv (suc current) ten)
    (accumulator + naturalMod (suc current) ten)

sumOfDigits : Nat → Nat
sumOfDigits x = sumOfDigitsWithFuel x x zero

countSumDivisibleBy-precond : Nat → Nat → Set
countSumDivisibleBy-precond n d = zero < d

isSumDivisibleBy : Nat → Nat → Bool
isSumDivisibleBy x d =
  natEqual (naturalMod (sumOfDigits x) d) zero

countLoop : Nat → Nat → Nat → Nat
countLoop zero accumulator d = accumulator
countLoop (suc i) accumulator d =
  if isSumDivisibleBy i d
  then countLoop i (suc accumulator) d
  else countLoop i accumulator d

countSumDivisibleBy :
  (n d : Nat) →
  countSumDivisibleBy-precond n d →
  Nat
countSumDivisibleBy n d h-precond =
  countLoop n zero d

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

matchingCount : Nat → Nat → Nat
matchingCount n d =
  listLength
    (filterList
      (λ x →
        natLess x n &&
        natEqual (naturalMod (sumOfDigits x) d) zero)
      (range n))

countSumDivisibleBy-postcond :
  (n d result : Nat) →
  countSumDivisibleBy-precond n d →
  Set
countSumDivisibleBy-postcond n d result h-precond =
  (natSubtract (matchingCount n d) result ≡ zero) ∧
  (result ≤ matchingCount n d)

countSumDivisibleBy-spec-satisfied : Set
countSumDivisibleBy-spec-satisfied =
  (n d : Nat) →
  (h-precond : countSumDivisibleBy-precond n d) →
  countSumDivisibleBy-postcond
    n
    d
    (countSumDivisibleBy n d h-precond)
    h-precond
