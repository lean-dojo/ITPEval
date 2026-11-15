-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_252:
-- the remainder of 7 factorial modulo 23. This file contains no proof.

module mathd-numbertheory-252 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-252 : Set
mathd-numbertheory-252 =
  naturalMod (factorial 7) 23 ≡ 3
