-- Statement-only formalization of Thousand Theorems artifact Q5445112
-- (thousand-theorems__lean4__Q5445112), "Fernique's theorem": every Gaussian
-- measure on a complete second-countable real normed space exponentially
-- integrates a positive multiple of the squared norm. This file contains no proof.

import Mathlib.Probability.Distributions.Gaussian.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real Topology

namespace Q5445112

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Fernique's theorem for a Gaussian measure on a second-countable normed space. -/
theorem exists_integrable_exp_sq (μ : Measure E) [IsGaussian μ] :
    ∃ C, 0 < C ∧ Integrable (fun x ↦ rexp (C * ‖x‖ ^ 2)) μ := sorry

end Q5445112
