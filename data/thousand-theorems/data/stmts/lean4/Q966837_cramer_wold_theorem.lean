-- Canonical Lean registration for Thousand Theorems artifact Q966837,
-- "Cramer-Wold theorem". The statement is copied exactly from
-- the imported `tendstoInDistribution_iff_tendstoInDistribution_inner`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Probability.CramerWold

@[expose] public section

namespace ThousandTheorems.Q966837

/-- The Mathlib statement selected as the canonical Lean form of Cramer-Wold theorem. -/
theorem canonical_statement : type_of% @tendstoInDistribution_iff_tendstoInDistribution_inner :=
  @tendstoInDistribution_iff_tendstoInDistribution_inner

end ThousandTheorems.Q966837
