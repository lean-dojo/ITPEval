-- Statement-only formalization of Thousand Theorems artifact Q727102
-- (thousand-theorems__lean4__Q727102), "Fermat's theorem (stationary points)":
-- the derivative of a real-valued function at a local extremum is zero, both
-- for functions on real normed spaces and for real functions. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

universe u

namespace Q727102

section Frechet

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {a : E}

/-- Fermat's theorem for the Fréchet derivative at a local extremum. -/
theorem fderiv_eq_zero (h : IsLocalExtr f a) : fderiv ℝ f a = 0 := sorry

end Frechet

section Real

variable {f : ℝ → ℝ} {a : ℝ}

/-- Fermat's theorem for the derivative of a real function at a local extremum. -/
theorem deriv_eq_zero (h : IsLocalExtr f a) : deriv f a = 0 := sorry

end Real

end Q727102
