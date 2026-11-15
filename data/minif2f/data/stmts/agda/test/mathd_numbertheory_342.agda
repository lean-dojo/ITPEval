-- Statement-only formalization of miniF2F test problem mathd_numbertheory_342. This file
-- contains no proof.

module mathd-numbertheory-342 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-342 : Set
mathd-numbertheory-342 =
  naturalMod 54 6 ≡ zero
