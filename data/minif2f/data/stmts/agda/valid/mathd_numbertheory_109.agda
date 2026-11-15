-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_109. This file
-- contains no proof.

module mathd-numbertheory-109 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

sumFromOne : Nat → (Nat → Nat) → Nat
sumFromOne zero term = zero
sumFromOne (suc n) term = sumFromOne n term + term (suc n)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-109 : Set
mathd-numbertheory-109 =
  (v : Nat → Nat) →
  ((n : Nat) → v n ≡ 2 * n - 1) →
  naturalMod (sumFromOne 100 v) 7 ≡ 4
