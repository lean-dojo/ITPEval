-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__068, "Sum of an Arithmetic Series": twice the
-- inclusive natural-number arithmetic-series sum. This file contains no proof.

module ArithmeticSeries where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

sumThrough : Nat → (Nat → Nat) → Nat
sumThrough zero term = term zero
sumThrough (suc n) term =
  sumThrough n term + term (suc n)

sum-of-an-arithmetic-series : Set
sum-of-an-arithmetic-series =
  (a d n : Nat) →
  2 * sumThrough n (λ i → a + i * d)
    ≡ suc n * (2 * a + n * d)
