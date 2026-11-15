-- Statement-only formalization of Hundred Theorems artifact 047, "The Central Limit Theorem": independent identically distributed real random variables with finite variance have normalized partial-sum laws converging weakly to the standard normal distribution. This file contains no proof.
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

theorem central_limit_theorem_zero_mean
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : Measure ℝ) (σ : ℝ)
    (hX_measurable : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X P)
    (hX_mean_zero : ∀ n, ∫ ω, X n ω ∂P = 0)
    (hσ_pos : 0 < σ)
    (hX_square_integrable : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) P)
    (hX_variance : ∀ n, variance (X n) P = σ ^ 2)
    (hX_distrib : ∀ n, P.map (X n) = μ) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto
        (fun n ↦ ∫ x, f x ∂P.map (fun ω ↦
          (∑ i ∈ range n, X i ω) / Real.sqrt ((n : ℝ) * σ ^ 2)))
        atTop
        (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  sorry

theorem central_limit_theorem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : Measure ℝ) (m σ : ℝ)
    (hX_measurable : ∀ n, Measurable (X n))
    (hX_indep : iIndepFun X P)
    (hX_mean : ∀ n, ∫ ω, X n ω ∂P = m)
    (hσ_pos : 0 < σ)
    (hX_square_integrable : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) P)
    (hX_variance : ∀ n, variance (X n) P = σ ^ 2)
    (hX_distrib : ∀ n, P.map (X n) = μ) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto
        (fun n ↦ ∫ x, f x ∂P.map (fun ω ↦
          (∑ i ∈ range n, (X i ω - m)) / Real.sqrt ((n : ℝ) * σ ^ 2)))
        atTop
        (𝓝 (∫ x, f x ∂gaussianReal 0 1)) := by
  sorry
