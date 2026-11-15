-- Canonical Lean registration for Thousand Theorems artifact Q190391,
-- "Central limit theorem". The statement is copied exactly from
-- the imported `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Probability.CentralLimitTheorem

@[expose] public section

namespace ThousandTheorems.Q190391

/-- The Mathlib statement selected as the canonical Lean form of Central limit theorem. -/
theorem canonical_statement : type_of% @ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub :=
  @ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub

end ThousandTheorems.Q190391
