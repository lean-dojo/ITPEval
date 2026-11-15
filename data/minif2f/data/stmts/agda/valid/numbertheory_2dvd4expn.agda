-- Statement-only formalization of miniF2F valid problem numbertheory_2dvd4expn. This file
-- contains no proof.

module numbertheory_2dvd4expn where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _∣_
infixr 8 _^_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

numbertheory_2dvd4expn : Set
numbertheory_2dvd4expn =
  (n : Nat) →
  Not (n ≡ zero) →
  2 ∣ (4 ^ n)
