-- Statement-only formalization of VERINA corpus artifact verina_basic_11,
-- catalog title "lastDigit": a deterministic natural-number program returns
-- the remainder modulo ten and is connected to its digit-range and
-- truncated-subtraction correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic11 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

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

lastDigit-precond : Nat → Set
lastDigit-precond n = Top

lastDigit :
  (n : Nat) →
  lastDigit-precond n →
  Nat
lastDigit n h-precond =
  naturalMod n ten

lastDigit-postcond :
  (n result : Nat) →
  lastDigit-precond n →
  Set
lastDigit-postcond n result h-precond =
  ((zero ≤ result) ∧ (result < ten)) ∧
  ((natSubtract (naturalMod n ten) result ≡ zero) ∧
   (natSubtract result (naturalMod n ten) ≡ zero))

lastDigit-spec-satisfied : Set
lastDigit-spec-satisfied =
  (n : Nat) →
  (h-precond : lastDigit-precond n) →
  lastDigit-postcond
    n
    (lastDigit n h-precond)
    h-precond
