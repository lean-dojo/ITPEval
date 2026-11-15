/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Integrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.FloorPow
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The strong law of large numbers

We prove the strong law of large numbers, in `ProbabilityTheory.strong_law_ae`:
If `X n` is a sequence of independent identically distributed integrable random
variables, then `∑ i ∈ range n, X i / n` converges almost surely to `𝔼[X 0]`.
We give here the strong version, due to Etemadi, that only requires pairwise independence.

This file also contains the Lᵖ version of the strong law of large numbers provided by
`ProbabilityTheory.strong_law_Lp` which shows `∑ i ∈ range n, X i / n` converges in Lᵖ to
`𝔼[X 0]` provided `X n` is independent identically distributed and is Lᵖ.

## Implementation

The main point is to prove the result for real-valued random variables, as the general case
of Banach-space-valued random variables follows from this case and approximation by simple
functions. The real version is given in `ProbabilityTheory.strong_law_ae_real`.

We follow the proof by Etemadi
[Etemadi, *An elementary proof of the strong law of large numbers*][etemadi_strong_law],
which goes as follows.

It suffices to prove the result for nonnegative `X`, as one can prove the general result by
splitting a general `X` into its positive part and negative part.
Consider `Xₙ` a sequence of nonnegative integrable identically distributed pairwise independent
random variables. Let `Yₙ` be the truncation of `Xₙ` up to `n`. We claim that
* Almost surely, `Xₙ = Yₙ` for all but finitely many indices. Indeed, `∑ ℙ (Xₙ ≠ Yₙ)` is bounded by
  `1 + 𝔼[X]` (see `sum_prob_mem_Ioc_le` and `tsum_prob_mem_Ioi_lt_top`).
* Let `c > 1`. Along the sequence `n = c ^ k`, then `(∑_{i=0}^{n-1} Yᵢ - 𝔼[Yᵢ])/n` converges almost
  surely to `0`. This follows from a variance control, as
```
  ∑_k ℙ (|∑_{i=0}^{c^k - 1} Yᵢ - 𝔼[Yᵢ]| > c^k ε)
    ≤ ∑_k (c^k ε)^{-2} ∑_{i=0}^{c^k - 1} Var[Yᵢ]    (by Markov inequality)
    ≤ ∑_i (C/i^2) Var[Yᵢ]                           (as ∑_{c^k > i} 1/(c^k)^2 ≤ C/i^2)
    ≤ ∑_i (C/i^2) 𝔼[Yᵢ^2]
    ≤ 2C 𝔼[X^2]                                     (see `sum_variance_truncation_le`)
```
* As `𝔼[Yᵢ]` converges to `𝔼[X]`, it follows from the two previous items and Cesàro that, along
  the sequence `n = c^k`, one has `(∑_{i=0}^{n-1} Xᵢ) / n → 𝔼[X]` almost surely.
* To generalize it to all indices, we use the fact that `∑_{i=0}^{n-1} Xᵢ` is nondecreasing and
  that, if `c` is close enough to `1`, the gap between `c^k` and `c^(k+1)` is small.
-/

@[expose] public section


noncomputable section

open MeasureTheory Filter Finset Asymptotics

open Set (indicator)

open scoped Topology MeasureTheory ProbabilityTheory ENNReal NNReal

open scoped Function -- required for scoped `on` notation

namespace ProbabilityTheory

/-! ### Prerequisites on truncations -/


section Truncation

variable {α : Type*}

/-- Truncating a real-valued function to the interval `(-A, A]`. -/
def truncation (f : α → ℝ) (A : ℝ) :=
  indicator (Set.Ioc (-A) A) id ∘ f

variable {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

theorem _root_.MeasureTheory.AEStronglyMeasurable.truncation (hf : AEStronglyMeasurable f μ)
    {A : ℝ} : AEStronglyMeasurable (truncation f A) μ := by sorry
theorem abs_truncation_le_bound (f : α → ℝ) (A : ℝ) (x : α) : |truncation f A x| ≤ |A| := by sorry
theorem truncation_zero (f : α → ℝ) : truncation f 0 = 0 := by simp [truncation]; rfl

theorem abs_truncation_le_abs_self (f : α → ℝ) (A : ℝ) (x : α) : |truncation f A x| ≤ |f x| := by sorry
theorem truncation_eq_self {f : α → ℝ} {A : ℝ} {x : α} (h : |f x| < A) :
    truncation f A x = f x := by sorry
theorem truncation_eq_of_nonneg {f : α → ℝ} {A : ℝ} (h : ∀ x, 0 ≤ f x) :
    truncation f A = indicator (Set.Ioc 0 A) id ∘ f := by sorry
theorem truncation_nonneg {f : α → ℝ} (A : ℝ) {x : α} (h : 0 ≤ f x) : 0 ≤ truncation f A x :=
  Set.indicator_apply_nonneg fun _ => h

theorem _root_.MeasureTheory.AEStronglyMeasurable.memLp_truncation [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) {A : ℝ} {p : ℝ≥0∞} : MemLp (truncation f A) p μ :=
  MemLp.of_bound hf.truncation |A| (Eventually.of_forall fun _ => abs_truncation_le_bound _ _ _)

theorem _root_.MeasureTheory.AEStronglyMeasurable.integrable_truncation [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) {A : ℝ} : Integrable (truncation f A) μ := by sorry
theorem moment_truncation_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A : ℝ} (hA : 0 ≤ A)
    {n : ℕ} (hn : n ≠ 0) : ∫ x, truncation f A x ^ n ∂μ = ∫ y in -A..A, y ^ n ∂Measure.map f μ := by sorry
theorem moment_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable f μ) {A : ℝ}
    {n : ℕ} (hn : n ≠ 0) (h'f : 0 ≤ f) :
    ∫ x, truncation f A x ^ n ∂μ = ∫ y in 0..A, y ^ n ∂Measure.map f μ := by sorry
theorem integral_truncation_eq_intervalIntegral (hf : AEStronglyMeasurable f μ) {A : ℝ}
    (hA : 0 ≤ A) : ∫ x, truncation f A x ∂μ = ∫ y in -A..A, y ∂Measure.map f μ := by sorry
theorem integral_truncation_eq_intervalIntegral_of_nonneg (hf : AEStronglyMeasurable f μ) {A : ℝ}
    (h'f : 0 ≤ f) : ∫ x, truncation f A x ∂μ = ∫ y in 0..A, y ∂Measure.map f μ := by sorry
theorem integral_truncation_le_integral_of_nonneg (hf : Integrable f μ) (h'f : 0 ≤ f) {A : ℝ} :
    ∫ x, truncation f A x ∂μ ≤ ∫ x, f x ∂μ := by sorry
theorem tendsto_integral_truncation {f : α → ℝ} (hf : Integrable f μ) :
    Tendsto (fun A => ∫ x, truncation f A x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by sorry
theorem IdentDistrib.truncation {β : Type*} [MeasurableSpace β] {ν : Measure β} {f : α → ℝ}
    {g : β → ℝ} (h : IdentDistrib f g μ ν) {A : ℝ} :
    IdentDistrib (truncation f A) (truncation g A) μ ν :=
  h.comp (measurable_id.indicator measurableSet_Ioc)

end Truncation

section StrongLawAeReal

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

section MomentEstimates

theorem sum_prob_mem_Ioc_le {X : Ω → ℝ} (hint : Integrable X) (hnonneg : 0 ≤ X) {K : ℕ} {N : ℕ}
    (hKN : K ≤ N) :
    ∑ j ∈ range K, ℙ {ω | X ω ∈ Set.Ioc (j : ℝ) N} ≤ ENNReal.ofReal (𝔼[X] + 1) := by sorry
theorem tsum_prob_mem_Ioi_lt_top {X : Ω → ℝ} (hint : Integrable X) (hnonneg : 0 ≤ X) :
    (∑' j : ℕ, ℙ {ω | X ω ∈ Set.Ioi (j : ℝ)}) < ∞ := by sorry
theorem sum_variance_truncation_le {X : Ω → ℝ} (hint : Integrable X) (hnonneg : 0 ≤ X) (K : ℕ) :
    ∑ j ∈ range K, ((j : ℝ) ^ 2)⁻¹ * 𝔼[truncation X j ^ 2] ≤ 2 * 𝔼[X] := by sorry
end MomentEstimates

/-! Proof of the strong law of large numbers (almost sure version, assuming only
pairwise independence) for nonnegative random variables, following Etemadi's proof. -/
section StrongLawNonneg

variable (X : ℕ → Ω → ℝ) (hint : Integrable (X 0))
  (hindep : Pairwise (IndepFun on X)) (hident : ∀ i, IdentDistrib (X i) (X 0))
  (hnonneg : ∀ i ω, 0 ≤ X i ω)

include hint hindep hident hnonneg in
/-- The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers (with respect to
the truncated expectation) along the sequence `c^n`, for any `c > 1`, up to a given `ε > 0`.
This follows from a variance control. -/
theorem strong_law_aux1 {c : ℝ} (c_one : 1 < c) {ε : ℝ} (εpos : 0 < ε) : ∀ᵐ ω, ∀ᶠ n : ℕ in atTop, := by sorry
theorem strong_law_aux2 {c : ℝ} (c_one : 1 < c) :
    ∀ᵐ ω, (fun n : ℕ => ∑ i ∈ range ⌊c ^ n⌋₊, truncation (X i) i ω -
      𝔼[∑ i ∈ range ⌊c ^ n⌋₊, truncation (X i) i]) =o[atTop] fun n : ℕ => (⌊c ^ n⌋₊ : ℝ) := by sorry
theorem strong_law_aux3 :
    (fun n => 𝔼[∑ i ∈ range n, truncation (X i) i] - n * 𝔼[X 0]) =o[atTop] ((↑) : ℕ → ℝ) := by sorry
theorem strong_law_aux4 {c : ℝ} (c_one : 1 < c) :
    ∀ᵐ ω, (fun n : ℕ => ∑ i ∈ range ⌊c ^ n⌋₊, truncation (X i) i ω - ⌊c ^ n⌋₊ * 𝔼[X 0]) =o[atTop]
    fun n : ℕ => (⌊c ^ n⌋₊ : ℝ) := by sorry
theorem strong_law_aux5 :
    ∀ᵐ ω, (fun n : ℕ => ∑ i ∈ range n, truncation (X i) i ω - ∑ i ∈ range n, X i ω) =o[atTop]
    fun n : ℕ => (n : ℝ) := by sorry
theorem strong_law_aux6 {c : ℝ} (c_one : 1 < c) :
    ∀ᵐ ω, Tendsto (fun n : ℕ => (∑ i ∈ range ⌊c ^ n⌋₊, X i ω) / ⌊c ^ n⌋₊) atTop (𝓝 𝔼[X 0]) := by sorry
theorem strong_law_aux7 :
    ∀ᵐ ω, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 𝔼[X 0]) := by sorry
end StrongLawNonneg

/-- **Strong law of large numbers**, almost sure version: if `X n` is a sequence of independent
identically distributed integrable real-valued random variables, then `∑ i ∈ range n, X i / n`
converges almost surely to `𝔼[X 0]`. We give here the strong version, due to Etemadi, that only
requires pairwise independence. Superseded by `strong_law_ae`, which works for random variables
taking values in any Banach space. -/
theorem strong_law_ae_real {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ i ∈ range n, X i ω) / n) atTop (𝓝 μ[X 0]) := by sorry
end StrongLawAeReal

section StrongLawVectorSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

open Set TopologicalSpace

/-- Preliminary lemma for the strong law of large numbers for vector-valued random variables:
the composition of the random variables with a simple function satisfies the strong law of large
numbers. -/
lemma strong_law_ae_simpleFunc_comp (X : ℕ → Ω → E) (h' : Measurable (X 0))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (φ : SimpleFunc E E) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, φ (X i ω))) atTop (𝓝 μ[φ ∘ (X 0)]) := by sorry
variable [BorelSpace E]

/-- Preliminary lemma for the strong law of large numbers for vector-valued random variables,
assuming measurability in addition to integrability. This is weakened to ae measurability in
the full version `ProbabilityTheory.strong_law_ae`. -/
lemma strong_law_ae_of_measurable
    (X : ℕ → Ω → E) (hint : Integrable (X 0) μ) (h' : StronglyMeasurable (X 0))
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0]) := by sorry
theorem strong_law_ae (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω)) atTop (𝓝 μ[X 0]) := by sorry
end StrongLawVectorSpace

section StrongLawLp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Strong law of large numbers**, Lᵖ version: if `X n` is a sequence of independent
identically distributed random variables in Lᵖ, then `n⁻¹ • ∑ i ∈ range n, X i`
converges in `Lᵖ` to `𝔼[X 0]`. -/
theorem strong_law_Lp {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (X : ℕ → Ω → E)
    (hℒp : MemLp (X 0) p μ) (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun (n : ℕ) => eLpNorm (fun ω => (n : ℝ)⁻¹ • (∑ i ∈ range n, X i ω) - μ[X 0]) p μ)
      atTop (𝓝 0) := by sorry
end StrongLawLp

end ProbabilityTheory
