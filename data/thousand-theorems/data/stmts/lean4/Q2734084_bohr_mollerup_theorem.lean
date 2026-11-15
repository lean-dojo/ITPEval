-- Canonical Lean registration for Thousand Theorems artifact Q2734084,
-- "Bohr-Mollerup theorem". The statement is copied exactly from
-- the imported `Real.eq_Gamma_of_log_convex`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

@[expose] public section

namespace ThousandTheorems.Q2734084

/-- The Mathlib statement selected as the canonical Lean form of Bohr-Mollerup theorem. -/
theorem canonical_statement : type_of% @Real.eq_Gamma_of_log_convex :=
  @Real.eq_Gamma_of_log_convex

end ThousandTheorems.Q2734084
