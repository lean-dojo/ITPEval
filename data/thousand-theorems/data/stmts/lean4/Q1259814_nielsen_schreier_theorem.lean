-- Statement-only formalization of Thousand Theorems artifact Q1259814
-- (thousand-theorems__lean4__Q1259814), "Nielsen–Schreier theorem": every subgroup
-- of a free group is itself free. This file contains no proof.

module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

@[expose] public section

universe u

namespace Q1259814

/-- The Nielsen–Schreier theorem: every subgroup of a free group is free. -/
theorem subgroupIsFreeOfIsFree_statement {G : Type u} [Group G] [IsFreeGroup G]
    (H : Subgroup G) : IsFreeGroup H := sorry

end Q1259814
