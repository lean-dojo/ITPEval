-- Statement-only formalization of miniF2F test problem mathd_numbertheory_277. This file
-- contains no proof.

module mathd-numbertheory-277 where

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
      (k : Nat) →
      a ∣ k →
      b ∣ k →
      l ∣ k

mathd-numbertheory-277 : Set
mathd-numbertheory-277 =
  (m n : Nat) →
  IsGCD m n 6 →
  IsLCM m n 126 →
  60 ≤ m + n
