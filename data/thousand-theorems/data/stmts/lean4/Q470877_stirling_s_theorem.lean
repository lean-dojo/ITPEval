-- Statement-only formalization of Thousand Theorems artifact Q470877
-- (thousand-theorems__lean4__Q470877), "Stirling's theorem": the normalized
-- factorial sequence tends to the square root of pi. This file contains no proof.

module

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Defs

open scoped Topology Real Nat

open Filter Real

namespace Q470877

/-- The normalized factorial sequence appearing in Stirling's theorem. -/
noncomputable def stirlingSeq (n : ℕ) : ℝ :=
  n ! / (√(2 * n : ℝ) * (n / exp 1) ^ n)

/-- Stirling's theorem: the normalized factorial sequence converges to `√π`. -/
theorem tendsto_stirlingSeq_sqrt_pi : Tendsto stirlingSeq atTop (𝓝 (√π)) := sorry

end Q470877
