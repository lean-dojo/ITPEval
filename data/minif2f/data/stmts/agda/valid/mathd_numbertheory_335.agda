-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_335:
-- if a natural number has remainder 5 modulo 7, then five times it has remainder
-- 4 modulo 7. This file contains no proof.

module mathd-numbertheory-335 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-335 : Set
mathd-numbertheory-335 =
  (n : Nat) →
  naturalMod n 7 ≡ 5 →
  naturalMod (5 * n) 7 ≡ 4
