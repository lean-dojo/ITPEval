-- Canonical Lean registration for Thousand Theorems artifact Q1551745,
-- "Binomial inverse theorem". The statement is copied exactly from
-- the imported `Matrix.invOf_add_mul_mul'`; the body reuses Mathlib's checked proof.

module

public import Mathlib.LinearAlgebra.Matrix.Invertible

@[expose] public section

namespace ThousandTheorems.Q1551745

/-- The Mathlib statement selected as the canonical Lean form of Binomial inverse theorem. -/
theorem canonical_statement : type_of% @Matrix.invOf_add_mul_mul' :=
  @Matrix.invOf_add_mul_mul'

end ThousandTheorems.Q1551745
