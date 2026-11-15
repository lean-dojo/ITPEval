-- Statement-only formalization of miniF2F test problem mathd_numbertheory_175. This file
-- contains no proof.

module mathd-numbertheory-175 where

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

mathd-numbertheory-175 : Set
mathd-numbertheory-175 =
  naturalMod (2 ^ 2010) 10 ≡ 4
