-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__069, "Greatest Common Divisor Algorithm": the
-- Euclidean algorithm computes a greatest common divisor of two natural numbers.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _∣_ _↔_
infixr 5 _×_

record _×_ (A B : Set) : Set where
  field
    left : A
    right : B

record _↔_ (A B : Set) : Set where
  field
    forward : A → B
    backward : B → A

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat → Nat → Nat → Nat
gcdWithFuel zero a b = a
gcdWithFuel (suc fuel) a zero = a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

euclideanGCD : Nat → Nat → Nat
euclideanGCD a b =
  gcdWithFuel (suc (a + b)) a b

greatest-common-divisor-algorithm : Set
greatest-common-divisor-algorithm =
  (a b d : Nat) →
  (d ∣ euclideanGCD a b) ↔ ((d ∣ a) × (d ∣ b))
