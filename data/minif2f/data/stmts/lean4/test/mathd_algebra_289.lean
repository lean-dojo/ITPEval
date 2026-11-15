-- Statement-only formalization of miniF2F test problem mathd_algebra_289. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_289
  (k t m n : ℕ)
  (h₀ : Nat.Prime m ∧ Nat.Prime n)
  (h₁ : t < k)
  (h₂ : k ^ 2 + n = m * k)
  (h₃ : t ^ 2 + n = m * t) :
  m^n + n^m + k^t + t^k = 20 := by sorry
