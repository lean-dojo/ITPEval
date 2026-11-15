-- Statement-only formalization of VERINA corpus artifact verina_basic_43,
-- catalog title "sumOfFourthPowerOfOddNumbers": a deterministic natural-number
-- recursion sums the fourth powers of the first n odd numbers and is connected
-- to its closed-form polynomial correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic43 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

record Top : Set where
  constructor top

natPower : Nat → Nat → Nat
natPower base zero = suc zero
natPower base (suc exponent) =
  base * natPower base exponent

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

sumOfFourthPowerOfOddNumbers-precond : Nat → Set
sumOfFourthPowerOfOddNumbers-precond n = Top

sumOfFourthPowerOfOddNumbers :
  (n : Nat) →
  sumOfFourthPowerOfOddNumbers-precond n →
  Nat
sumOfFourthPowerOfOddNumbers zero h-precond = zero
sumOfFourthPowerOfOddNumbers (suc n) h-precond =
  let previous =
        sumOfFourthPowerOfOddNumbers n h-precond
      nextOdd = (2 * n) + 1
  in
    previous + natPower nextOdd 4

sumOfFourthPowerOfOddNumbers-postcond :
  (n result : Nat) →
  sumOfFourthPowerOfOddNumbers-precond n →
  Set
sumOfFourthPowerOfOddNumbers-postcond n result h-precond =
  15 * result ≡
    (n * ((2 * n) + 1)) *
      (natSubtract
        (natSubtract
          (7 + (24 * natPower n 3))
          (12 * natPower n 2))
        (14 * n))

sumOfFourthPowerOfOddNumbers-spec-satisfied : Set
sumOfFourthPowerOfOddNumbers-spec-satisfied =
  (n : Nat) →
  (h-precond : sumOfFourthPowerOfOddNumbers-precond n) →
  sumOfFourthPowerOfOddNumbers-postcond
    n
    (sumOfFourthPowerOfOddNumbers n h-precond)
    h-precond
