-- Canonical Lean registration for Thousand Theorems artifact Q338886,
-- "Divergence theorem". The statement is copied exactly from
-- the imported `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`; the body reuses Mathlib's checked proof.

module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

@[expose] public section

namespace ThousandTheorems.Q338886

/-- The Mathlib statement selected as the canonical Lean form of Divergence theorem. -/
theorem canonical_statement : type_of% @MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable :=
  @MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable

end ThousandTheorems.Q338886
