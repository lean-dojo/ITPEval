-- Statement-only formalization of miniF2F test problem mathd_numbertheory_235. This file
-- contains no proof.

module mathd-numbertheory-235 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-235 : Set
mathd-numbertheory-235 =
  naturalMod (29 * 79 + 31 * 81) 10 ≡ 2
