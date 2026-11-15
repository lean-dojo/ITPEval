-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_200. This file
-- contains no proof.

module mathd-numbertheory-200 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-200 : Set
mathd-numbertheory-200 =
  naturalMod 139 11 ≡ 7
