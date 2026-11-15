-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_269:
-- the sum 2005^2 + 2005^0 + 2005^0 + 2005^5 has remainder 52 modulo 100.
-- This file contains no proof.

module mathd-numbertheory-269 where

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

mathd-numbertheory-269 : Set
mathd-numbertheory-269 =
  naturalMod (2005 ^ 2 + 2005 ^ 0 + 2005 ^ 0 + 2005 ^ 5) 100 ≡ 52
