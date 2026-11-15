-- Statement-only formalization of Thousand Theorems artifact Q1191709
-- (thousand-theorems__lean4__Q1191709), "Egorov's theorem": on a measurable set
-- of finite measure, an almost-everywhere convergent family of strongly measurable
-- functions converges uniformly outside an arbitrarily small measurable subset.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

@[expose] public section

open MeasureTheory NNReal ENNReal Topology
open Set Filter TopologicalSpace

namespace Q1191709

variable {α β ι : Type*} {m : MeasurableSpace α} [PseudoEMetricSpace β] {μ : Measure α}
variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]
  {f : ι → α → β} {g : α → β} {s : Set α}

/-- Egorov's theorem for strongly measurable functions on a finite-measure measurable set. -/
theorem tendstoUniformlyOn_of_ae_tendsto (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  sorry

end Q1191709
