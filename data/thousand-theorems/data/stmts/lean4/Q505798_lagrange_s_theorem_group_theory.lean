-- Statement-only formalization of Thousand Theorems artifact Q505798
-- (thousand-theorems__lean4__Q505798), "Lagrange's theorem (group theory)":
-- the order of a subgroup divides the order of its ambient group. This file contains no proof.

module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

variable {α : Type*} [Group α]

namespace Subgroup

/-- Lagrange's theorem: the order of a subgroup divides the order of its ambient group. -/
theorem card_subgroup_dvd_card (s : Subgroup α) : Nat.card s ∣ Nat.card α := sorry

end Subgroup
