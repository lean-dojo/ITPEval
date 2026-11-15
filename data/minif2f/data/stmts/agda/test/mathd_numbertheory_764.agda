-- Statement-only formalization of miniF2F test problem mathd_numbertheory_764:
-- for a prime p at least 7, the sum modulo p of products of consecutive modular
-- inverses from 1 through p - 2 is 2. This file contains no proof.

module mathd-numbertheory-764 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

infix 4 _≤_ _∣_
infixr 3 _∨_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

modularInverse : Nat → Nat → Nat
modularInverse value modulus =
  naturalMod (value ^ (modulus - 2)) modulus

sumInverseProducts : Nat → Nat → Nat
sumInverseProducts modulus zero = zero
sumInverseProducts modulus (suc count) =
  sumInverseProducts modulus count +
  modularInverse (suc count) modulus *
  modularInverse (suc (suc count)) modulus

mathd-numbertheory-764 : Set
mathd-numbertheory-764 =
  (p : Nat) →
  Prime p →
  7 ≤ p →
  naturalMod (sumInverseProducts p (p - 2)) p ≡ 2
