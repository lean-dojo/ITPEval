-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_458. This file
-- contains no proof.

module mathd-numbertheory-458 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-458 : Set
mathd-numbertheory-458 =
  (n : Nat) →
  naturalMod n 8 ≡ 7 →
  naturalMod n 4 ≡ 3
