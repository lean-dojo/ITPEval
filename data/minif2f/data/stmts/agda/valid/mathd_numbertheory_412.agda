-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_412. This file
-- contains no proof.

module mathd-numbertheory-412 where

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

mathd-numbertheory-412 : Set
mathd-numbertheory-412 =
  (x y : Nat) →
  naturalMod x 19 ≡ 4 →
  naturalMod y 19 ≡ 7 →
  naturalMod ((x + 1) ^ 2 * (y + 5) ^ 3) 19 ≡ 13
