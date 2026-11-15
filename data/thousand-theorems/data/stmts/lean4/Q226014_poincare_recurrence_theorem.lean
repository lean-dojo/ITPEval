-- Canonical Lean registration for Thousand Theorems artifact Q226014,
-- "Poincare recurrence theorem". The statement is copied exactly from
-- the imported `MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Dynamics.Ergodic.Conservative

@[expose] public section

namespace ThousandTheorems.Q226014

/-- The Mathlib statement selected as the canonical Lean form of Poincare recurrence theorem. -/
theorem canonical_statement : type_of% @MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem :=
  @MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem

end ThousandTheorems.Q226014
