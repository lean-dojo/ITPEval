-- Statement-only formalization of miniF2F valid problem mathd_algebra_282. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem mathd_algebra_282 (f : ℝ → ℝ) (h₀ : ∀ x : ℝ, ¬ (Irrational x) → f x = abs (Int.floor x))
  (h₁ : ∀ x, Irrational x → f x = (Int.ceil x) ^ 2) :
  f ((8 : ℝ) ^ ((1 : ℝ) / 3)) + f (-Real.pi) + f (Real.sqrt 50) + f (9 / 2) = 79 := by sorry
