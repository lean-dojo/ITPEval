-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_961:
-- the natural-number remainder of 2003 divided by 11 is 1. This file contains no proof.

module mathd-numbertheory-961 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-961 : Set
mathd-numbertheory-961 =
  naturalMod 2003 11 ≡ 1
