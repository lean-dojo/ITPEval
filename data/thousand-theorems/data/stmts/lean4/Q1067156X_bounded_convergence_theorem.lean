-- Statement-only formalization of Thousand Theorems artifact Q1067156X
-- (thousand-theorems__lean4__Q1067156X), "Bounded convergence theorem": uniformly
-- bounded continuous nonnegative functions converging almost everywhere along a countably
-- generated filter have convergent lower Lebesgue integrals. This file contains no proof.

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

@[expose] public section

open BoundedContinuousFunction Filter MeasureTheory Topology
open scoped ENNReal NNReal Topology

namespace Q1067156X

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- Finite measures bundled exactly as a measure together with its finiteness instance. -/
def FiniteMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsFiniteMeasure μ }

/-- Bounded convergence along a countably generated filter for a finite measure. -/
theorem tendsto_lintegral_nn_filter_of_le_const {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (μ : Measure Ω) [IsFiniteMeasure μ]
    {fs : ι → Ω →ᵇ ℝ≥0} {c : ℝ≥0}
    (fs_le_const : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c) {f : Ω → ℝ≥0}
    (fs_lim : ∀ᵐ ω : Ω ∂μ, Tendsto (fun i ↦ fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i ↦ ∫⁻ ω, fs i ω ∂μ) L (𝓝 (∫⁻ ω, f ω ∂μ)) := sorry

/-- The sequence and pointwise-convergence specialization of bounded convergence. -/
theorem tendsto_lintegral_nn_of_le_const (μ : FiniteMeasure Ω)
    {fs : ℕ → Ω →ᵇ ℝ≥0} {c : ℝ≥0} (fs_le_const : ∀ n ω, fs n ω ≤ c)
    {f : Ω → ℝ≥0} (fs_lim : ∀ ω, Tendsto (fun n ↦ fs n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n ↦ ∫⁻ ω, fs n ω ∂μ.1) atTop (𝓝 (∫⁻ ω, f ω ∂μ.1)) := sorry

end Q1067156X
