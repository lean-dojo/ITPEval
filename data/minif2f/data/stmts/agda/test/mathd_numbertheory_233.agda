-- Statement-only formalization of miniF2F test problem mathd_numbertheory_233. This file
-- contains no proof.

module mathd-numbertheory-233 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; _<_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-233 : Set
mathd-numbertheory-233 =
  (b : Nat) →
  (b < 11 * 11) ≡ true →
  naturalMod (b * 24) (11 * 11) ≡ 1 →
  b ≡ 116
