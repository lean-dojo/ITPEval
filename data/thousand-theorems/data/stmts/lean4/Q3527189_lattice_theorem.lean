-- Statement-only formalization of Thousand Theorems artifact Q3527189
-- (thousand-theorems__lean4__Q3527189), "Lattice theorem": for normal subgroups
-- N ≤ M of a group G, the iterated quotient (G / N) / (M / N) is
-- multiplicatively equivalent to G / M. This file contains no proof.

module

public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

universe u

namespace Q3527189

variable {G : Type u} [Group G] (N M : Subgroup G) [N.Normal] [M.Normal]

/-- Noether's third isomorphism theorem for groups. -/
def quotientQuotientEquivQuotientStatement (h : N ≤ M) :
    (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M := sorry

end Q3527189
