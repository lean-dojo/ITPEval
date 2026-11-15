-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_37:
-- the least common multiple of 9999 and 100001 is 90900909. This file contains no proof.

module mathd-numbertheory-37 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)

infix 4 _∣_

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

record IsLCM (a b l : Nat) : Set where
  field
    lcm-left-divides : a ∣ l
    lcm-right-divides : b ∣ l
    least-common-multiple :
      (m : Nat) →
      a ∣ m →
      b ∣ m →
      l ∣ m

mathd-numbertheory-37 : Set
mathd-numbertheory-37 =
  IsLCM 9999 100001 90900909
