-- Statement-only formalization of miniF2F valid problem imo_1988_p6. This file contains no
-- proof.

module imo-1988-p6 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_ _∣_

data _<_ : Nat → Nat → Set where
  zero<suc : {n : Nat} → zero < suc n
  suc<suc  : {m n : Nat} → m < n → suc m < suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

record Exists {A : Set} (P : A → Set) : Set where
  field
    witness  : A
    evidence : P witness

square : Nat → Nat
square n = n * n

imo-1988-p6 : Set
imo-1988-p6 =
  (a b : Nat) →
  zero < a →
  zero < b →
  (a * b + 1) ∣ (square a + square b) →
  Exists
    (λ x →
      (a * b + 1) * square x ≡
      square a + square b)
