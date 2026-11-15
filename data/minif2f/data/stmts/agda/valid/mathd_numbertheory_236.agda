-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_236:
-- the natural-number remainder of 1999 raised to the 2000th power modulo 5 is 1.
-- This file contains no proof.

module mathd-numbertheory-236 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-236 : Set
mathd-numbertheory-236 =
  naturalMod (1999 ^ 2000) 5 ≡ 1
