-- Canonical Lean registration for Thousand Theorems artifact Q20971632,
-- "Lie's theorem". The statement is copied exactly from
-- the imported `LieModule.exists_nontrivial_weightSpace_of_isSolvable`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Algebra.Lie.LieTheorem

@[expose] public section

namespace ThousandTheorems.Q20971632

/-- The Mathlib statement selected as the canonical Lean form of Lie's theorem. -/
theorem canonical_statement : type_of% @LieModule.exists_nontrivial_weightSpace_of_isSolvable :=
  @LieModule.exists_nontrivial_weightSpace_of_isSolvable

end ThousandTheorems.Q20971632
