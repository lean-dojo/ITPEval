-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_102. This file
-- contains no proof.

module mathd-numbertheory-102 where

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

mathd-numbertheory-102 : Set
mathd-numbertheory-102 =
  naturalMod (2 ^ 8) 5 ≡ 1
