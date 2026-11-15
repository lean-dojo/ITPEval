-- Canonical Lean registration for Thousand Theorems artifact Q859122,
-- "Cauchy-Hadamard theorem". The statement is copied exactly from
-- the imported `FormalMultilinearSeries.radius_inv_eq_limsup`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Analysis.Analytic.RadiusLiminf

@[expose] public section

namespace ThousandTheorems.Q859122

/-- The Mathlib statement selected as the canonical Lean form of Cauchy-Hadamard theorem. -/
theorem canonical_statement : type_of% @FormalMultilinearSeries.radius_inv_eq_limsup :=
  @FormalMultilinearSeries.radius_inv_eq_limsup

end ThousandTheorems.Q859122
