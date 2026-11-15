-- Statement-only formalization of miniF2F valid problem amc12a_2020_p13. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem amc12a_2020_p13 (a b c : ℕ) (n : ℝ) (h₀ : 0 < n) (h₁ : n ≠ 1)
  (h₂ : 1 < a ∧ 1 < b ∧ 1 < c)
  (h₃ :
    (n * (n * n ^ ((1 : ℝ) / c)) ^ ((1 : ℝ) / b)) ^ ((1 : ℝ) / a) =
      (n ^ 25) ^ ((1 : ℝ) / 36)) :
  b = 3 := by sorry
