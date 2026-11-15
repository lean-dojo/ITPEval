-- Canonical Lean registration for Thousand Theorems artifact Q1660147,
-- "Mazur-Ulam theorem". The statement is copied exactly from
-- the imported `IsometryEquiv.coe_toRealAffineIsometryEquiv`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Analysis.Normed.Affine.MazurUlam

@[expose] public section

namespace ThousandTheorems.Q1660147

/-- The Mathlib statement selected as the canonical Lean form of Mazur-Ulam theorem. -/
theorem canonical_statement : type_of% @IsometryEquiv.coe_toRealAffineIsometryEquiv :=
  @IsometryEquiv.coe_toRealAffineIsometryEquiv

end ThousandTheorems.Q1660147
