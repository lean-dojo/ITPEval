-- Statement-only formalization of Thousand Theorems artifact Q2275191
-- (thousand-theorems__lean4__Q2275191), "Lebesgue differentiation theorem":
-- normalized local lower Lebesgue integrals of an almost-everywhere measurable
-- function converge almost everywhere to its value along a Vitali family. This file contains no proof.

module

public import Mathlib.MeasureTheory.Covering.VitaliFamily
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal MeasureTheory Topology

namespace Q2275191

variable {α : Type*} [PseudoMetricSpace α] {m0 : MeasurableSpace α} {μ : Measure α}
  (v : VitaliFamily μ)

/-- Lebesgue differentiation for lower integrals along a Vitali family. -/
theorem ae_tendsto_lintegral_div [SecondCountableTopology α] [BorelSpace α]
    [IsLocallyFiniteMeasure μ] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (h'f : (∫⁻ y, f y ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ a)
      (v.filterAt x) (𝓝 (f x)) := sorry

end Q2275191
