-- Statement-only formalization of miniF2F test problem mathd_numbertheory_99:
-- a natural-number modular arithmetic implication modulo 47. This file contains no proof.

module mathd-numbertheory-99 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-99 : Set
mathd-numbertheory-99 =
  (n : Nat) →
  naturalMod (2 * n) 47 ≡ 15 →
  naturalMod n 47 ≡ 31
