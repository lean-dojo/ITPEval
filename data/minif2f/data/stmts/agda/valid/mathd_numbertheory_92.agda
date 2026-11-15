-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_92. This file
-- contains no proof.

module mathd-numbertheory-92 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-92 : Set
mathd-numbertheory-92 =
  (n : Nat) →
  naturalMod (5 * n) 17 ≡ 8 →
  naturalMod n 17 ≡ 5
