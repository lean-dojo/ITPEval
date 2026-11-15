-- Statement-only formalization of miniF2F test problem mathd_numbertheory_239: the sum of
-- the natural numbers from 1 through 12 has remainder 2 modulo 4. This file contains no
-- proof.

module mathd-numbertheory-239 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

sumFromOne : Nat → Nat
sumFromOne zero = zero
sumFromOne (suc n) = sumFromOne n + suc n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-239 : Set
mathd-numbertheory-239 =
  naturalMod (sumFromOne 12) 4 ≡ 2
