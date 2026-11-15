-- Statement-only formalization of Thousand Theorems artifact Q2027347
-- (thousand-theorems__lean4__Q2027347), "Optional stopping theorem": under a
-- sigma-finite filtration, a strongly adapted integrable real-valued process is a
-- submartingale exactly when expected stopped values are monotone for ordered bounded
-- stopping times. This file contains no proof.

module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ}

/-- The optional stopping theorem for real-valued discrete-time submartingales. -/
theorem submartingale_iff_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ ∀ τ π : Ω → ℕ∞, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 π →
      τ ≤ π → (∃ N : ℕ, ∀ x, π x ≤ N) →
        μ[stoppedValue f τ] ≤ μ[stoppedValue f π] := sorry

end MeasureTheory
