-- Statement-only formalization of Thousand Theorems artifact Q182505
-- (thousand-theorems__lean4__Q182505), "Bayes' theorem": for a finite measure
-- and measurable events, the conditional probability of one event given the
-- other satisfies the measure-theoretic Bayes identity. This file contains no proof.

module

public import Mathlib.Probability.ConditionalProbability

@[expose] public section

open MeasureTheory

namespace Q182505

variable {Ω : Type*} [MeasurableSpace Ω] {s t : Set Ω}

/-- Bayes' theorem for conditional probabilities under a finite measure. -/
theorem bayes_theorem_statement (hms : MeasurableSet s) (hmt : MeasurableSet t)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    ProbabilityTheory.cond μ s t =
      (μ s)⁻¹ * ProbabilityTheory.cond μ t s * μ t := sorry

end Q182505
