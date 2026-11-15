-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_30:
-- the sum of the squares from 33818 through 33822 is divisible by 17. This file contains no proof.

module mathd-numbertheory-30 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-30 : Set
mathd-numbertheory-30 =
  naturalMod
    (33818 ^ 2 + 33819 ^ 2 + 33820 ^ 2 + 33821 ^ 2 + 33822 ^ 2)
    17
  ≡ 0
