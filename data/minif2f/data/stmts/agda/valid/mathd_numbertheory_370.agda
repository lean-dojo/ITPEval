-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_370. This file
-- contains no proof.

module mathd-numbertheory-370 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-370 : Set
mathd-numbertheory-370 =
  (n : Nat) →
  naturalMod n 7 ≡ 3 →
  naturalMod (2 * n + 1) 7 ≡ 0
