-- Statement-only formalization of Thousand Theorems artifact Q1153584
-- (thousand-theorems__lean4__Q1153584), "Monotone convergence theorem":
-- almost-everywhere monotone convergence for extended-nonnegative Lebesgue integrals
-- and antitone convergence for integrable real-valued Bochner integrals.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open Filter Topology
open scoped ENNReal MeasureTheory
open MeasureTheory

namespace Q1153584

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Monotone convergence for extended-nonnegative Lebesgue integrals. -/
theorem lintegral_tendsto_of_tendsto_of_monotone
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫⁻ x, f n x ∂μ) atTop (𝓝 (∫⁻ x, F x ∂μ)) := sorry

/-- Monotone convergence in antitone form for real-valued Bochner integrals. -/
theorem integral_tendsto_of_tendsto_of_antitone
    {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ)
    (hF : Integrable F μ)
    (h_mono : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := sorry

end Q1153584
