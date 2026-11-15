-- Statement-only formalization of miniF2F test problem mathd_numbertheory_483. This file
-- contains no proof.

module mathd-numbertheory-483 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-483 : Set
mathd-numbertheory-483 =
  (a : Nat → Nat) →
  a 1 ≡ 1 →
  a 2 ≡ 1 →
  ((n : Nat) → a (n + 2) ≡ a (n + 1) + a n) →
  naturalMod (a 100) 4 ≡ 3
