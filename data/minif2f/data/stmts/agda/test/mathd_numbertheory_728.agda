-- Statement-only formalization of miniF2F test problem mathd_numbertheory_728. This file
-- contains no proof.

module mathd-numbertheory-728 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-728 : Set
mathd-numbertheory-728 =
  naturalMod ((29 ^ 13) - (5 ^ 13)) 7 ≡ 3
