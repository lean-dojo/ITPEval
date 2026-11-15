-- Statement-only formalization of miniF2F test problem mathd_numbertheory_254. This file
-- contains no proof.

module mathd-numbertheory-254 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-254 : Set
mathd-numbertheory-254 =
  naturalMod (239 + 174 + 83) 10 ≡ 6
