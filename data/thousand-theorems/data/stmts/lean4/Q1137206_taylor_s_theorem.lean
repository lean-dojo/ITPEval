-- Statement-only formalization of Thousand Theorems artifact Q1137206
-- (thousand-theorems__lean4__Q1137206), "Taylor's theorem": under the source
-- differentiability hypotheses on a real interval, the Taylor remainder has both
-- Lagrange and Cauchy mean-value forms. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

open scoped Interval Topology Nat

open Set

namespace Q1137206

/-- Taylor's theorem with the Lagrange form of the remainder. -/
theorem taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hx : x₀ < x) (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := sorry

/-- Taylor's theorem with the Cauchy form of the remainder. -/
theorem taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hx : x₀ < x) (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x') ^ n / n ! * (x - x₀) := sorry

end Q1137206
