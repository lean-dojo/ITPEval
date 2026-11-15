-- Statement-only formalization of miniF2F test problem mathd_numbertheory_457:
-- factorial divisibility forcing a lower bound on a positive natural number.
-- This file contains no proof.

module mathd-numbertheory-457 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _<_ _∣_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

mathd-numbertheory-457 : Set
mathd-numbertheory-457 =
  (n : Nat) →
  zero < n →
  80325 ∣ factorial n →
  17 ≤ n
