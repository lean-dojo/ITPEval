-- Canonical Lean registration for Thousand Theorems artifact Q7525341,
-- "Sion's minimax theorem". The statement is copied exactly from
-- the imported `Sion.minimax`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Topology.Sion

@[expose] public section

namespace ThousandTheorems.Q7525341

/-- The Mathlib statement selected as the canonical Lean form of Sion's minimax theorem. -/
theorem canonical_statement : type_of% @Sion.minimax :=
  @Sion.minimax

end ThousandTheorems.Q7525341
