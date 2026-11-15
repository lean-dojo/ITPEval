-- Statement-only formalization of miniF2F test problem mathd_numbertheory_247. This file
-- contains no proof.

module mathd-numbertheory-247 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-247 : Set
mathd-numbertheory-247 =
  (n : Nat) →
  naturalMod (3 * n) 11 ≡ 2 →
  naturalMod n 11 ≡ 8
