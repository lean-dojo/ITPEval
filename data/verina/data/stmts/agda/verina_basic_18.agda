-- Statement-only formalization of VERINA corpus artifact verina_basic_18,
-- catalog title "sumOfDigits": a deterministic natural-number program sums
-- the decimal digits of its input and is connected to the corresponding
-- decimal-representation correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic18 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; div-helper; mod-helper)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

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

sumOfDigits-loop : Nat → Nat → Nat → Nat
sumOfDigits-loop zero current accumulator = accumulator
sumOfDigits-loop (suc fuel) zero accumulator = accumulator
sumOfDigits-loop (suc fuel) current@(suc _) accumulator =
  sumOfDigits-loop
    fuel
    (naturalDiv current ten)
    (accumulator + naturalMod current ten)

sumOfDigits-precond : Nat → Set
sumOfDigits-precond n = Top

sumOfDigits :
  (n : Nat) →
  sumOfDigits-precond n →
  Nat
sumOfDigits n h-precond =
  sumOfDigits-loop n n zero

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

sumList : List Nat → Nat
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

decimalDigitSum : Nat → Nat
decimalDigitSum n = sumList (decimalDigits n)

sumOfDigits-postcond :
  (n result : Nat) →
  sumOfDigits-precond n →
  Set
sumOfDigits-postcond n result h-precond =
  (natSubtract result (decimalDigitSum n) ≡ zero) ∧
  (natSubtract (decimalDigitSum n) result ≡ zero)

sumOfDigits-spec-satisfied : Set
sumOfDigits-spec-satisfied =
  (n : Nat) →
  (h-precond : sumOfDigits-precond n) →
  sumOfDigits-postcond
    n
    (sumOfDigits n h-precond)
    h-precond
