-- Statement-only formalization of VERINA corpus artifact verina_advanced_72,
-- catalog title "singleDigitPrimeFactor": a deterministic program returns the
-- first divisor among 2, 3, 5, and 7 (or 0 when none applies), connected to
-- its natural-number correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced72 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _∈_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

data _∈_ (x : Nat) : List Nat → Set where
  here : {xs : List Nat} → x ∈ (x ∷ xs)
  there : {y : Nat} {xs : List Nat} → x ∈ xs → x ∈ (y ∷ xs)

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

natModWithFuel : Nat → Nat → Nat → Nat
natModWithFuel zero n divisor = n
natModWithFuel (suc fuel) n divisor =
  if natLess n divisor
  then n
  else
    natModWithFuel
      fuel
      (natSubtract n divisor)
      divisor

natMod : Nat → Nat → Nat
natMod n zero = n
natMod n divisor@(suc _) =
  natModWithFuel n n divisor

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

one : Nat
one = suc zero

two : Nat
two = suc one

three : Nat
three = suc two

four : Nat
four = suc three

five : Nat
five = suc four

six : Nat
six = suc five

seven : Nat
seven = suc six

properSingleDigitPrimes : List Nat
properSingleDigitPrimes =
  two ∷ three ∷ five ∷ seven ∷ []

allowedResults : List Nat
allowedResults =
  zero ∷ properSingleDigitPrimes

singleDigitPrimeFactor-precond : Nat → Set
singleDigitPrimeFactor-precond n = Top

singleDigitPrimeFactor :
  (n : Nat) →
  singleDigitPrimeFactor-precond n →
  Nat
singleDigitPrimeFactor n h-precond =
  if natEqual n zero
  then zero
  else
    if natEqual (natMod n two) zero
    then two
    else
      if natEqual (natMod n three) zero
      then three
      else
        if natEqual (natMod n five) zero
        then five
        else
          if natEqual (natMod n seven) zero
          then seven
          else zero

singleDigitPrimeFactor-postcond :
  (n : Nat) →
  (result : Nat) →
  singleDigitPrimeFactor-precond n →
  Set
singleDigitPrimeFactor-postcond n result h-precond =
  (result ∈ allowedResults) ∧
  ((result ≡ zero) →
    ((n ≡ zero) ∨
      All
        (λ divisor →
          Not (natMod n divisor ≡ zero))
        properSingleDigitPrimes)) ∧
  (Not (result ≡ zero) →
    Not (n ≡ zero) ∧
    (natMod n result ≡ zero) ∧
    All
      (λ candidate →
        candidate ∈ properSingleDigitPrimes →
        Not (natMod n candidate ≡ zero))
      (range result))

singleDigitPrimeFactor-spec-satisfied : Set
singleDigitPrimeFactor-spec-satisfied =
  (n : Nat) →
  (h-precond : singleDigitPrimeFactor-precond n) →
  singleDigitPrimeFactor-postcond
    n
    (singleDigitPrimeFactor n h-precond)
    h-precond
