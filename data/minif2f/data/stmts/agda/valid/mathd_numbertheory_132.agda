-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_132:
-- 2004 modulo 12 equals zero. This file contains no proof.

module mathd-numbertheory-132 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-132 : Set
mathd-numbertheory-132 =
  naturalMod 2004 12 ≡ 0
