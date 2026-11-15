-- Statement-only formalization of Thousand Theorems artifact Q570779
-- (thousand-theorems__lean4__Q570779), "Vieta's formulas": over any commutative
-- semiring, the product of the polynomial factors X + C r from a multiset equals
-- the sum formed from its elementary symmetric functions. This file contains no proof.

module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

@[expose] public section

open Finset Polynomial

namespace Q570779

variable {R : Type*} [CommSemiring R]

/-- The product form of Vieta's formula for a multiset over a commutative semiring. -/
theorem prod_X_add_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun r => X + C r).prod =
      ∑ j ∈ Finset.range (Multiset.card s + 1),
        C (s.esymm j) * X ^ (Multiset.card s - j) := sorry

end Q570779
