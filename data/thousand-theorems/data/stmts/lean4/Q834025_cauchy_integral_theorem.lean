-- Statement-only formalization of Thousand Theorems artifact Q834025
-- (thousand-theorems__lean4__Q834025), "Cauchy integral theorem": for a complex-valued
-- function continuous on a closed disc and complex differentiable in its interior away
-- from a countable set, the circle integral of `f z / (z - w)` equals `2πi f(w)`.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section

open Set MeasureTheory Metric
open scoped Real

namespace Complex.Q834025

/-- The Cauchy integral formula for a function differentiable off a countable set. -/
theorem cauchy_integral_theorem {R : ℝ} {c w : ℂ} {s : Set ℂ}
    (hs : s.Countable) (hw : w ∈ ball c R) {f : ℂ → ℂ}
    (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z / (z - w)) = 2 * π * I * f w := sorry

end Complex.Q834025
