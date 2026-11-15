-- Statement-only formalization of miniF2F valid problem amc12a_2003_p25. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2003_p25 (a b : ℝ) (f : ℝ → ℝ) (h₀ : 0 < b)
  (h₁ : ∀ x, f x = Real.sqrt (a * x ^ 2 + b * x))
  (h₂ : {x | 0 ≤ a * x ^ 2 + b * x} = f '' {x | 0 ≤ a * x ^ 2 + b * x}) :
  a = 0 ∨ a = -4 := by sorry
