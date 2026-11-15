-- Statement-only formalization of "The Irrationality of the Square Root of 2" from Hundred
-- Theorems item 001. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _*_)

data ⊥ : Set where

infix 4 _≠_

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

irrational-square-root-of-two : Set
irrational-square-root-of-two =
  (numerator denominator : Nat) →
  denominator ≠ zero →
  numerator * numerator ≡ 2 * (denominator * denominator) →
  ⊥
