-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_169. This file
-- contains no proof.

module mathd-numbertheory-169 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _∣_

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

record IsGCD (a b g : Nat) : Set where
  field
    gcd-divides-left : g ∣ a
    gcd-divides-right : g ∣ b
    greatest-common-divisor :
      (d : Nat) →
      d ∣ a →
      d ∣ b →
      d ∣ g

mathd-numbertheory-169 : Set
mathd-numbertheory-169 =
  IsGCD (factorial 20) 200000 40000
