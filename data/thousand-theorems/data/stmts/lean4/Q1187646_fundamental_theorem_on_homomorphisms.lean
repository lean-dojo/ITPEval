-- Statement-only formalization of Thousand Theorems artifact Q1187646
-- (thousand-theorems__lean4__Q1187646), "Fundamental theorem on homomorphisms":
-- every group homomorphism induces a multiplicative equivalence from the quotient
-- of its domain by its kernel to its range. This file contains no proof.

module

public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

universe u v

namespace Q1187646

open MonoidHom

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- The first isomorphism theorem for groups, stated as the induced multiplicative equivalence. -/
noncomputable def quotientKerEquivRange_statement (φ : G →* H) :
    G ⧸ ker φ ≃* range φ := sorry

end Q1187646
