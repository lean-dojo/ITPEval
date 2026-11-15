-- Statement-only formalization of miniF2F test problem mathd_algebra_314. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_314
  (n : ℕ)
  (h₀ : n = 11) :
  ((1 : ℝ) / 4) ^ (n + 1) * (2 : ℝ) ^ (2 * n) = 1 / 4 := by sorry
