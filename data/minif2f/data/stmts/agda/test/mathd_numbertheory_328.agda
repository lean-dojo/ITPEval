-- Statement-only formalization of miniF2F test problem mathd_numbertheory_328. This file
-- contains no proof.

module mathd-numbertheory-328 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-328 : Set
mathd-numbertheory-328 =
  naturalMod (5 ^ 999999) 7 ≡ 6
