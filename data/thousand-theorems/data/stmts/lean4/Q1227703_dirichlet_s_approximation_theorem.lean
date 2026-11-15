-- Statement-only formalization of Thousand Theorems artifact Q1227703
-- (thousand-theorems__lean4__Q1227703), "Dirichlet's approximation theorem":
-- on an additive circle of positive circumference, for every point and positive
-- natural number n, some multiplier from 1 through n has norm at most the
-- circumference divided by n + 1. This file contains no proof.

module

public import Mathlib.Analysis.Normed.Group.AddCircle

@[expose] public section

open Set

namespace Q1227703

variable {T : ℝ} [Fact (0 < T)]

/-- Dirichlet's approximation theorem for the additive circle. -/
theorem exists_norm_nsmul_le (ξ : AddCircle T) {n : ℕ} (hn : 0 < n) :
    ∃ j ∈ Icc 1 n, ‖j • ξ‖ ≤ T / ↑(n + 1) := sorry

end Q1227703
