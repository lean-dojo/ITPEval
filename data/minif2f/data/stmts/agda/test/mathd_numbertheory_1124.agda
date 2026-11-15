-- Statement-only formalization of miniF2F test problem mathd_numbertheory_1124. This file
-- contains no proof.

module mathd-numbertheory-1124 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _∣_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

mathd-numbertheory-1124 : Set
mathd-numbertheory-1124 =
  (n : Nat) →
  n ≤ 9 →
  18 ∣ (374 * 10 + n) →
  n ≡ 4
