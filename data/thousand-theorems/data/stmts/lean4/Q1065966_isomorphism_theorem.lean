-- Statement-only formalization of Thousand Theorems artifact Q1065966
-- (thousand-theorems__lean4__Q1065966), "Isomorphism theorem": the canonical
-- first, second, and third isomorphisms for quotient groups. This file contains no proof.

module

public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

universe u v

namespace Q1065966

open MonoidHom

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- The quotient by a homomorphism's kernel is multiplicatively equivalent to its range. -/
noncomputable def quotientKerEquivRange_statement (φ : G →* H) :
    G ⧸ ker φ ≃* range φ := sorry

/-- For normal `N`, `H / (H ∩ N)` is multiplicatively equivalent to `(H ⊔ N) / N`. -/
noncomputable def quotientInfEquivProdNormalQuotient_statement
    (H N : Subgroup G) [N.Normal] :
    H ⧸ N.subgroupOf H ≃* (H ⊔ N : Subgroup G) ⧸ N.subgroupOf (H ⊔ N) := sorry

/-- If `N ≤ M` are normal, then `(G / N) / (M / N)` is equivalent to `G / M`. -/
def quotientQuotientEquivQuotient_statement
    (N M : Subgroup G) [N.Normal] [M.Normal] (h : N ≤ M) :
    (G ⧸ N) ⧸ M.map (QuotientGroup.mk' N) ≃* G ⧸ M := sorry

end Q1065966
