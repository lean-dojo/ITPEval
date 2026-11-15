-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_126. This file
-- contains no proof.

module mathd-numbertheory-126 where

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

record IsLCM (a b l : Nat) : Set where
  field
    lcm-left-divides : a ∣ l
    lcm-right-divides : b ∣ l
    least-common-multiple :
      (m : Nat) →
      a ∣ m →
      b ∣ m →
      l ∣ m

mathd-numbertheory-126 : Set
mathd-numbertheory-126 =
  (x a : Nat) →
  zero < x →
  zero < a →
  IsGCD a 40 (x + 3) →
  IsLCM a 40 (x * (x + 3)) →
  ((b : Nat) →
    zero < b →
    IsGCD b 40 (x + 3) →
    IsLCM b 40 (x * (x + 3)) →
    a ≤ b) →
  a ≡ 8
