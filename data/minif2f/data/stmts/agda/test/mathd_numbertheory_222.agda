-- Statement-only formalization of miniF2F test problem mathd_numbertheory_222. This file
-- contains no proof.

module mathd-numbertheory-222 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)

infix 4 _∣_

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

mathd-numbertheory-222 : Set
mathd-numbertheory-222 =
  (b : Nat) →
  IsLCM 120 b 3720 →
  IsGCD 120 b 8 →
  b ≡ 248
