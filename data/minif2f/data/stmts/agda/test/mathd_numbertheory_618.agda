-- Statement-only formalization of miniF2F test problem mathd_numbertheory_618:
-- a nontrivial gcd of consecutive values of x^2 - x + 41 forces a positive
-- natural input to be at least 41. This file contains no proof.

module mathd-numbertheory-618 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_)

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

record HasGCDGreaterThanOne (a b : Nat) : Set where
  field
    gcd : Nat
    greater-than-one : 1 < gcd
    is-gcd : IsGCD a b gcd

mathd-numbertheory-618 : Set
mathd-numbertheory-618 =
  (n : Nat) →
  zero < n →
  (p : Nat → Nat) →
  ((x : Nat) → p x ≡ (x * x - x) + 41) →
  HasGCDGreaterThanOne (p n) (p (n + 1)) →
  41 ≤ n
