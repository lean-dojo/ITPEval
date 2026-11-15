-- Statement-only formalization of miniF2F test problem mathd_numbertheory_12. This file
-- contains no proof.

module mathd-numbertheory-12 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

countDivisibleFrom : Nat → Nat → Nat → Nat
countDivisibleFrom divisor start zero = zero
countDivisibleFrom divisor start (suc length)
  with natEqual (naturalMod start divisor) zero
... | true =
  suc (countDivisibleFrom divisor (suc start) length)
... | false =
  countDivisibleFrom divisor (suc start) length

mathd-numbertheory-12 : Set
mathd-numbertheory-12 =
  countDivisibleFrom 20 15 71 ≡ 4
