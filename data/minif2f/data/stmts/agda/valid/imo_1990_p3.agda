-- Statement-only formalization of miniF2F valid problem imo_1990_p3: if a natural number n
-- is at least 2 and n squared divides 2 to the power n plus 1, then n = 3. This file
-- contains no proof.

module imo-1990-p3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _∣_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

imo-1990-p3 : Set
imo-1990-p3 =
  (n : Nat) →
  2 ≤ n →
  (n ^ 2) ∣ (2 ^ n + 1) →
  n ≡ 3
