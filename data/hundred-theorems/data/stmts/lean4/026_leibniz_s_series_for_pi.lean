/-
Copyright (c) 2020 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Jeremy Tan
-/
module

public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-! ### Leibniz's series for `π` -/

public section

namespace Real

open Filter Finset

open scoped Topology

/-- **Leibniz's series for `π`**. The alternating sum of odd number reciprocals is `π / 4`,
proved by using Abel's limit theorem to extend the Maclaurin series of `arctan` to 1. -/
theorem tendsto_sum_pi_div_four :
    Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1)) atTop (𝓝 (π / 4)) := by sorry
end Real
