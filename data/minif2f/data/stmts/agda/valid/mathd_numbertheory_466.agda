-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_466:
-- the sum of the natural numbers below 11 has remainder 1 modulo 9. This file
-- contains no proof.

module mathd-numbertheory-466 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

sumBelow : Nat → Nat
sumBelow zero = zero
sumBelow (suc n) = sumBelow n + n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-466 : Set
mathd-numbertheory-466 =
  naturalMod (sumBelow 11) 9 ≡ 1
