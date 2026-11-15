-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_202. This file
-- contains no proof.

module mathd-numbertheory-202 where

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

mathd-numbertheory-202 : Set
mathd-numbertheory-202 =
  naturalMod (19 ^ 19 + 99 ^ 99) 10 ≡ 8
