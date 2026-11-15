-- Statement-only formalization of miniF2F valid problem induction_divisibility_9div10tonm1.
-- This file contains no proof.

module induction_divisibility_9div10tonm1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _≤_ _<_ _∣_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

induction_divisibility_9div10tonm1 : Set
induction_divisibility_9div10tonm1 =
  (n : Nat) →
  zero < n →
  9 ∣ (10 ^ n - 1)
