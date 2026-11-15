-- Statement-only formalization of Thousand Theorems artifact Q1149022
-- (thousand-theorems__lean4__Q1149022), "Fubini's theorem": for an integrable
-- function on a product of s-finite measure spaces, its Bochner integral equals
-- the corresponding iterated Bochner integral. This file contains no proof.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod

open scoped ENNReal MeasureTheory

open MeasureTheory

namespace Q1149022

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [SFinite μ] [SFinite ν]

/-- Fubini's theorem for the Bochner integral on a product measure. -/
theorem integral_prod (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := sorry

end Q1149022
