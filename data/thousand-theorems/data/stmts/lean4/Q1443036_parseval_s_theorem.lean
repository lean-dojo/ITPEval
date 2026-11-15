-- Canonical Lean registration for Thousand Theorems artifact Q1443036,
-- "Parseval's theorem". The statement is copied exactly from
-- the imported `tsum_sq_fourierCoeff`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section

namespace ThousandTheorems.Q1443036

/-- The Mathlib statement selected as the canonical Lean form of Parseval's theorem. -/
theorem canonical_statement : type_of% @tsum_sq_fourierCoeff :=
  @tsum_sq_fourierCoeff

end ThousandTheorems.Q1443036
