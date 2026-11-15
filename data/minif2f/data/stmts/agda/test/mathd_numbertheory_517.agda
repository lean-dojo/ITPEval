-- Statement-only formalization of miniF2F test problem mathd_numbertheory_517. This file
-- contains no proof.

module mathd-numbertheory-517 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-517 : Set
mathd-numbertheory-517 =
  naturalMod (121 * 122 * 123) 4 ≡ 2
