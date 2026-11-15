-- Statement-only formalization of miniF2F test problem
-- algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778. This file contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778
  (r : ℝ)
  (h₀ : ∃ x : ℝ, x ^ 3 = r ∧ x + 1 / x = 3) :
  r^3 + 1 / r^3 = 5778 := by sorry
