-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_81. This file
-- contains no proof.

module mathd-numbertheory-81 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-81 : Set
mathd-numbertheory-81 =
  naturalMod 71 3 ≡ 2
