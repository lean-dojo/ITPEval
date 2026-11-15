-- Statement-only formalization of miniF2F test problem mathd_numbertheory_435. This file
-- contains no proof.

module mathd-numbertheory-435 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

record IsGCD (a b g : Nat) : Set where
  field
    gcd-divides-left : g ∣ a
    gcd-divides-right : g ∣ b
    greatest-common-divisor :
      (d : Nat) →
      d ∣ a →
      d ∣ b →
      d ∣ g

mathd-numbertheory-435 : Set
mathd-numbertheory-435 =
  (k : Nat) →
  zero < k →
  ((n : Nat) → IsGCD (6 * n + k) (6 * n + 3) 1) →
  ((n : Nat) → IsGCD (6 * n + k) (6 * n + 2) 1) →
  ((n : Nat) → IsGCD (6 * n + k) (6 * n + 1) 1) →
  5 ≤ k
