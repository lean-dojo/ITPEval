-- Canonical Lean registration for Thousand Theorems artifact Q3527217,
-- "M. Riesz extension theorem". The statement is copied exactly from
-- the imported `riesz_extension`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Analysis.Convex.Cone.Extension

@[expose] public section

namespace ThousandTheorems.Q3527217

/-- The Mathlib statement selected as the canonical Lean form of M. Riesz extension theorem. -/
theorem canonical_statement : type_of% @riesz_extension :=
  @riesz_extension

end ThousandTheorems.Q3527217
