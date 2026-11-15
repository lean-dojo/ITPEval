-- Statement-only formalization of Thousand Theorems artifact Q5165492
-- (thousand-theorems__lean4__Q5165492), "Continuous mapping theorem": a continuous
-- function maps convergence in distribution to convergence in distribution of
-- the composed random variables. This file contains no proof.

module

/-
import Mathlib.MeasureTheory.Measure.Portmanteau
-/
import «/efs/robert/pde/itp-interop-main/corpus-extension/runs/20260816T230637Z-thousand-all10/tasks/thousand-theorems/lean4/Q5165492/compat5/Mathlib/MeasureTheory/Measure/Portmanteau»

open Filter
open scoped Topology

namespace MeasureTheory.Q5165492

variable {ι E Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} {X : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}
  [TopologicalSpace E]

structure TendstoInDistribution [OpensMeasurableSpace E] (X : (i : ι) → Ω i → E)
    (l : Filter ι) (Z : Ω' → E) (μ : (i : ι) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (μ' : Measure Ω') [IsProbabilityMeasure μ'] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z μ'
  tendsto : Tendsto (β := ProbabilityMeasure E)
    (fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l
    (𝓝 ⟨μ'.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)

/-- The continuous mapping theorem for convergence in distribution. -/
theorem continuous_mapping_theorem {F : Type*} [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] {g : E → F}
    (hg : Continuous g) (h : TendstoInDistribution X l Z μ μ') :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) μ μ' := sorry

end MeasureTheory.Q5165492
