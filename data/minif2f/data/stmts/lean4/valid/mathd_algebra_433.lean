-- Statement-only formalization of miniF2F valid problem mathd_algebra_433. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_433 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 3 * Real.sqrt (2 * x - 7) - 8) :
  f 8 = 1 := by sorry
