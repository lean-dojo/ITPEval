-- Statement-only formalization of Thousand Theorems artifact Q1752621
-- (thousand-theorems__lean4__Q1752621), "Sylvester's law of inertia": every
-- finite-dimensional real quadratic form is equivalent to a weighted sum of squares
-- whose weights are -1, 0, or 1. This file contains no proof.

module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

open Module QuadraticMap

namespace QuadraticForm

/-- Sylvester's law of inertia for real quadratic forms. -/
theorem equivalent_one_zero_neg_one_weighted_sum_squared
    {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) := sorry

end QuadraticForm
