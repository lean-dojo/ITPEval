-- Canonical Lean registration for Thousand Theorems artifact Q1140119,
-- "Morera's theorem". The statement is copied exactly from
-- the imported `Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Analysis.Complex.HasPrimitives

@[expose] public section

namespace ThousandTheorems.Q1140119

/-- The Mathlib statement selected as the canonical Lean form of Morera's theorem. -/
theorem canonical_statement : type_of% @Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn :=
  @Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn

end ThousandTheorems.Q1140119
