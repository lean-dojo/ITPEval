-- Statement-only formalization of Thousand Theorems artifact Q193286
-- (thousand-theorems__lean4__Q193286), "Rolle's theorem": a real function continuous
-- on a closed interval with equal endpoint values has derivative zero at some point
-- in the corresponding open interval. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Rolle

@[expose] public section

open Set

namespace Q193286

variable {f : ℝ → ℝ} {a b : ℝ}

/-- Rolle's theorem in terms of `deriv`. -/
theorem exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfI : f a = f b) : ∃ c ∈ Ioo a b, deriv f c = 0 := sorry

end Q193286
