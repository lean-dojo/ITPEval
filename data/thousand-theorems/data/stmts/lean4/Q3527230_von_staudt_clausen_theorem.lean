-- Canonical Lean registration for Thousand Theorems artifact Q3527230,
-- "Von Staudt-Clausen theorem". The statement is copied exactly from
-- the imported `Bernoulli.vonStaudt_clausen`; the body reuses Mathlib's checked proof.

module

public import Mathlib.NumberTheory.Bernoulli

@[expose] public section

namespace ThousandTheorems.Q3527230

/-- The Mathlib statement selected as the canonical Lean form of Von Staudt-Clausen theorem. -/
theorem canonical_statement : type_of% @Bernoulli.vonStaudt_clausen :=
  @Bernoulli.vonStaudt_clausen

end ThousandTheorems.Q3527230
