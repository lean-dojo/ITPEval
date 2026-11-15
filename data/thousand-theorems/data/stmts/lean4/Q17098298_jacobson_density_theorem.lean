-- Canonical Lean registration for Thousand Theorems artifact Q17098298,
-- "Jacobson density theorem". The statement is copied exactly from
-- the imported `jacobson_density`; the body reuses Mathlib's checked proof.

module

public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

namespace ThousandTheorems.Q17098298

/-- The Mathlib statement selected as the canonical Lean form of Jacobson density theorem. -/
theorem canonical_statement : type_of% @jacobson_density :=
  @jacobson_density

end ThousandTheorems.Q17098298
