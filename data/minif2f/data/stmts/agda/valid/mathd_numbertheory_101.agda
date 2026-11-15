-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_101. This file
-- contains no proof.

module mathd-numbertheory-101 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-101 : Set
mathd-numbertheory-101 =
  naturalMod (17 * 18) 4 ≡ 2
