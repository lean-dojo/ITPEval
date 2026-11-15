-- Statement-only formalization of miniF2F test problem mathd_algebra_208. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_208 :
  Real.sqrt 1000000 - (1000000 : ℝ) ^ ((1 : ℝ) / 3) = 900 := by sorry
