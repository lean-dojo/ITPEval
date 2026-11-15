-- Statement-only formalization of miniF2F test problem mathd_numbertheory_127:
-- the sum of 2^k for k from 0 through 100 has remainder 3 modulo 7.
-- This file contains no proof.

module mathd-numbertheory-127 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

sumFirst : Nat → (Nat → Nat) → Nat
sumFirst zero term = zero
sumFirst (suc n) term = sumFirst n term + term n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-127 : Set
mathd-numbertheory-127 =
  naturalMod (sumFirst 101 (λ k → 2 ^ k)) 7 ≡ 3
