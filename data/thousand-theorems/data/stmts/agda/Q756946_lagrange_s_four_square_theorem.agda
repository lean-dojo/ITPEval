-- Statement-only formalization of thousand-theorems corpus artifact Q756946
-- (thousand-theorems__agda__Q756946), "Lagrange's four-square theorem":
-- every natural number is a sum of four squares of natural numbers. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Q756946_lagrange_s_four_square_theorem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

square : Nat → Nat
square n = n * n

lagrange-four-square-theorem : Set
lagrange-four-square-theorem =
  (n : Nat) →
  Exists Nat (λ a →
    Exists Nat (λ b →
      Exists Nat (λ c →
        Exists Nat (λ d →
          square a + square b + square c + square d ≡ n))))
