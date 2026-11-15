-- Statement-only formalization of "Four Squares Theorem" from Hundred Theorems item 019. This
-- file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

square : Nat → Nat
square n = n * n

four-squares-theorem : Set
four-squares-theorem =
  (n : Nat) →
  Exists Nat (λ a →
    Exists Nat (λ b →
      Exists Nat (λ c →
        Exists Nat (λ d →
          n ≡ square a + square b + square c + square d))))
