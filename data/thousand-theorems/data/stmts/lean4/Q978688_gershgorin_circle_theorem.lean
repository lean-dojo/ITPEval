-- Statement-only formalization of Thousand Theorems artifact Q978688
-- (thousand-theorems__lean4__Q978688), "Gershgorin circle theorem": every
-- eigenvalue of a square matrix lies in a closed ball centered at a diagonal
-- entry, with radius given by the sum of the norms of the off-diagonal entries
-- in that row. This file contains no proof.

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

namespace Q978688

variable {K n : Type*} [NormedField K] [Fintype n] [DecidableEq n] {A : Matrix n n K}

/-- Gershgorin's circle theorem for an eigenvalue of a square matrix. -/
theorem eigenvalue_mem_ball {μ : K}
    (hμ : ∃ v : n → K, Matrix.mulVec A v = μ • v ∧ v ≠ 0) :
    ∃ k, μ ∈ Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖) := sorry

end Q978688
