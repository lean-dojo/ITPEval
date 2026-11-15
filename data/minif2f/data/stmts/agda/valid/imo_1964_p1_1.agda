-- Statement-only formalization of miniF2F valid problem imo_1964_p1_1. This file contains no
-- proof.

module imo-1964-p1-1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _∣_
infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

imo-1964-p1-1 : Set
imo-1964-p1-1 =
  (n : Nat) →
  7 ∣ (2 ^ n - 1) →
  3 ∣ n
