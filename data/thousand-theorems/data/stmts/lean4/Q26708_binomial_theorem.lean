-- Statement-only formalization of Thousand Theorems artifact Q26708
-- (thousand-theorems__lean4__Q26708), "Binomial theorem": the power of a sum
-- in a commutative semiring equals the finite sum of its binomial terms.
-- This file contains no proof.

module

public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

open Nat Finset

namespace Q26708

variable {R : Type*}

/-- The binomial theorem over a commutative semiring. -/
theorem binomial_theorem_statement [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m := sorry

end Q26708
