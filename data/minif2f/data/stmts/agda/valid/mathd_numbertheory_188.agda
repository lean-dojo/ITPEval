-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_188. This file
-- contains no proof.

module mathd-numbertheory-188 where

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

mathd-numbertheory-188 : Set
mathd-numbertheory-188 =
  IsGCD 180 168 12
