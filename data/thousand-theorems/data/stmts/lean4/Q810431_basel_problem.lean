-- Statement-only formalization of Thousand Theorems artifact Q810431
-- (thousand-theorems__lean4__Q810431), "Basel problem": the sum of the reciprocals
-- of the squares of the natural numbers is pi squared divided by six. This file
-- contains no proof.

module

import Mathlib.Analysis.PSeries

open scoped Real

namespace Q810431

/-- The Basel problem, expressed as convergence of the reciprocal-square series. -/
theorem hasSum_zeta_two :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  sorry

end Q810431
