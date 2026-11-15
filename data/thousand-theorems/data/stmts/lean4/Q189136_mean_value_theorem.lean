-- Statement-only formalization of Thousand Theorems artifact Q189136
-- (thousand-theorems__lean4__Q189136), "Mean value theorem": the derivative-form
-- Lagrange and Cauchy mean value theorems for real functions continuous on a closed
-- interval and differentiable on its interior. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open Set

namespace Q189136

/-- Lagrange's mean value theorem in terms of `deriv`. -/
theorem exists_deriv_eq_slope (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) := sorry

/-- Cauchy's mean value theorem in cross-multiplied `deriv` form. -/
theorem exists_ratio_deriv_eq_ratio_slope (f g : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) (hgd : DifferentiableOn ℝ g (Ioo a b)) :
    ∃ c ∈ Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c := sorry

end Q189136
