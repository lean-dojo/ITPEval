-- Statement-only formalization of miniF2F valid problem induction_divisibility_3div2tooddnp1.
-- This file contains no proof.

module induction_divisibility_3div2tooddnp1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _∣_
infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

induction_divisibility_3div2tooddnp1 : Set
induction_divisibility_3div2tooddnp1 =
  (n : Nat) →
  3 ∣ (2 ^ (2 * n + 1) + 1)
