-- Statement-only formalization of miniF2F test problem mathd_algebra_275. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_275
  (x : ℝ)
  (h : ((11 : ℝ) ^ ((1 : ℝ) / 4)) ^ (3 * x - 3) = 1 / 5) :
  ((11 : ℝ) ^ ((1 : ℝ) / 4)) ^ (6 * x + 2) = 121 / 25 := by sorry
