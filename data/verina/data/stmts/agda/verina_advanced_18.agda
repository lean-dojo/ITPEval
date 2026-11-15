-- Statement-only formalization of VERINA corpus artifact verina_advanced_18,
-- catalog title "isArmstrong": a deterministic natural-number program decides
-- whether a number equals the sum of its decimal digits raised to its digit count.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced18 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

infixr 3 _∧_

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

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

one : Nat
one = suc zero

ten : Nat
ten =
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

power : Nat → Nat → Nat
power base zero = one
power base (suc exponent) = base * power base exponent

countDigitsWithFuel : Nat → Nat → Nat → Nat
countDigitsWithFuel zero current accumulator = accumulator
countDigitsWithFuel (suc fuel) zero accumulator = accumulator
countDigitsWithFuel (suc fuel) current@(suc _) accumulator =
  countDigitsWithFuel
    fuel
    (naturalDiv current ten)
    (suc accumulator)

countDigits : Nat → Nat
countDigits n =
  if natEqual n zero
  then one
  else countDigitsWithFuel n n zero

isArmstrong-precond : Nat → Set
isArmstrong-precond n = Top

sumPowersWithFuel : Nat → Nat → Nat → Nat → Nat
sumPowersWithFuel zero current exponent accumulator = accumulator
sumPowersWithFuel (suc fuel) zero exponent accumulator = accumulator
sumPowersWithFuel
  (suc fuel)
  current@(suc _)
  exponent
  accumulator =
  let digit = naturalMod current ten
  in
    sumPowersWithFuel
      fuel
      (naturalDiv current ten)
      exponent
      (accumulator + power digit exponent)

sumPowers : Nat → Nat → Nat
sumPowers n exponent =
  sumPowersWithFuel n n exponent zero

isArmstrong :
  (n : Nat) →
  isArmstrong-precond n →
  Bool
isArmstrong n h-precond =
  let digitCount = countDigits n
  in natEqual (sumPowers n digitCount) n

digitsReversedWithFuel : Nat → Nat → List Nat
digitsReversedWithFuel zero current = []
digitsReversedWithFuel (suc fuel) zero = []
digitsReversedWithFuel (suc fuel) current@(suc _) =
  naturalMod current ten ∷
  digitsReversedWithFuel fuel (naturalDiv current ten)

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

decimalDigits : Nat → List Nat
decimalDigits zero = zero ∷ []
decimalDigits n@(suc _) =
  reverseList (digitsReversedWithFuel n n)

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

decimalPowerSum : Nat → Nat
decimalPowerSum n =
  foldLeft
    (λ accumulator digit →
      accumulator + power digit (countDigits n))
    zero
    (decimalDigits n)

isArmstrong-postcond :
  (n : Nat) →
  (result : Bool) →
  isArmstrong-precond n →
  Set
isArmstrong-postcond n result h-precond =
  let n′ = decimalPowerSum n
  in
    (IsTrue result → n ≡ n′) ∧
    (Not (IsTrue result) → Not (n ≡ n′))

isArmstrong-spec-satisfied : Set
isArmstrong-spec-satisfied =
  (n : Nat) →
  (h-precond : isArmstrong-precond n) →
  isArmstrong-postcond
    n
    (isArmstrong n h-precond)
    h-precond
