-- Canonical Lean registration for Thousand Theorems artifact Q5566491,
-- "Glaisher's theorem". The statement is copied exactly from
-- the imported `Nat.Partition.card_restricted_eq_card_countRestricted`; the body reuses Mathlib's checked proof.

module

public import Mathlib.Combinatorics.Enumerative.Partition.Glaisher

@[expose] public section

namespace ThousandTheorems.Q5566491

/-- The Mathlib statement selected as the canonical Lean form of Glaisher's theorem. -/
theorem canonical_statement : type_of% @Nat.Partition.card_restricted_eq_card_countRestricted :=
  @Nat.Partition.card_restricted_eq_card_countRestricted

end ThousandTheorems.Q5566491
