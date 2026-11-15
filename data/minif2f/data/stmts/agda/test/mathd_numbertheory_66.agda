-- Statement-only formalization of miniF2F test problem mathd_numbertheory_66:
-- the remainder of 194 upon division by 11 is 7. This file contains no proof.

module mathd-numbertheory-66 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-66 : Set
mathd-numbertheory-66 =
  naturalMod 194 11 ≡ 7
