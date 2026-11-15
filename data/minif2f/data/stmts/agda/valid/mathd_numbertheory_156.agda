-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_156:
-- the gcd of n + 7 and 2 * n + 1 is at most 13 for every positive natural n.
-- This file contains no proof.

module mathd-numbertheory-156 where

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

record HasGCDBoundedBy (a b bound : Nat) : Set where
  field
    gcd : Nat
    is-gcd : IsGCD a b gcd
    gcd-bound : gcd ≤ bound

mathd-numbertheory-156 : Set
mathd-numbertheory-156 =
  (n : Nat) →
  zero < n →
  HasGCDBoundedBy (n + 7) (2 * n + 1) 13
