-- Canonical Lean registration for Thousand Theorems artifact Q3527219,
-- "Weierstrass preparation theorem". The statement is copied exactly from
-- the imported `PowerSeries.exists_isWeierstrassFactorization`; the body reuses Mathlib's checked proof.

module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

@[expose] public section

namespace ThousandTheorems.Q3527219

/-- The Mathlib statement selected as the canonical Lean form of Weierstrass preparation theorem. -/
theorem canonical_statement : type_of% @PowerSeries.exists_isWeierstrassFactorization :=
  @PowerSeries.exists_isWeierstrassFactorization

end ThousandTheorems.Q3527219
