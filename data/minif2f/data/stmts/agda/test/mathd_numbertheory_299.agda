-- Statement-only formalization of miniF2F test problem mathd_numbertheory_299. This file
-- contains no proof.

module mathd-numbertheory-299 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-299 : Set
mathd-numbertheory-299 =
  naturalMod (1 * 3 * 5 * 7 * 9 * 11 * 13) 10 ≡ 5
