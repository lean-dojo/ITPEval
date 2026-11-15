-- Statement-only formalization of miniF2F valid problem imo_1964_p1_2. This file contains no
-- proof.

module imo-1964-p1-2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _∣_
infixr 8 _^_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

imo-1964-p1-2 : Set
imo-1964-p1-2 =
  (n : Nat) →
  Not (7 ∣ (2 ^ n + 1))
