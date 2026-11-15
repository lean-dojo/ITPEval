-- Statement-only formalization of miniF2F test problem mathd_numbertheory_85. This file
-- contains no proof.

module mathd-numbertheory-85 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

mathd-numbertheory-85 : Set
mathd-numbertheory-85 =
  1 * (3 ^ 3) + 2 * (3 ^ 2) + 2 * 3 + 2 ≡ 53
