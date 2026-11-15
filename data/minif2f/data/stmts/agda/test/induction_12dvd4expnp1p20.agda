-- Statement-only formalization of miniF2F test problem induction_12dvd4expnp1p20:
-- divisibility of 4^(n+1) + 20 by 12 for every natural n. This file contains no proof.

module induction_12dvd4expnp1p20 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

record Divides (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

induction-12dvd4expnp1p20 : Set
induction-12dvd4expnp1p20 =
  (n : Nat) →
  Divides 12 (4 ^ (n + 1) + 20)
