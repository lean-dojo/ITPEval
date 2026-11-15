-- Statement-only formalization of miniF2F test problem mathd_numbertheory_207. This file
-- contains no proof.

module mathd-numbertheory-207 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

mathd-numbertheory-207 : Set
mathd-numbertheory-207 =
  8 * 9 ^ 2 + 5 * 9 + 2 ≡ 695
