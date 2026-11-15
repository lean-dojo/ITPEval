-- Statement-only formalization of Thousand Theorems artifact Q1067156
-- (thousand-theorems__lean4__Q1067156), "Dominated convergence theorem": an almost
-- everywhere convergent sequence of almost everywhere strongly measurable functions dominated
-- by an integrable real-valued bound has convergent Bochner integrals. This file contains no proof.

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter TopologicalSpace

open scoped Topology

namespace Q1067156

variable {α G : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {m : MeasurableSpace α} {μ : Measure α}

/-- The dominated convergence theorem for the Bochner integral. -/
theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → G} {f : α → G}
    (bound : α → ℝ) (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ)
    (bound_integrable : Integrable bound μ) (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ) := sorry

end Q1067156
