-- Statement-only formalization of miniF2F test problem mathd_numbertheory_34. This file
-- contains no proof.

module mathd-numbertheory-34 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; _<_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-34 : Set
mathd-numbertheory-34 =
  (x : Nat) →
  (x < 100) ≡ true →
  naturalMod (x * 9) 100 ≡ 1 →
  x ≡ 89
