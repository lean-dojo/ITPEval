-- Canonical Lean registration for Thousand Theorems artifact Q7208500,
-- "Poisson limit theorem". The statement is copied exactly from
-- the imported `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

@[expose] public section

namespace ThousandTheorems.Q7208500

/-- The Mathlib statement selected as the canonical Lean form of Poisson limit theorem. -/
theorem canonical_statement : type_of% @ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop :=
  @ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop

end ThousandTheorems.Q7208500
