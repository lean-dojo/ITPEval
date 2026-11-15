-- Statement-only formalization of Thousand Theorems artifact Q2226800
-- (thousand-theorems__lean4__Q2226800), "Schur-Zassenhaus theorem": a normal
-- subgroup whose order is coprime to its index has a left complement.
-- This file contains no proof.

module

public import Mathlib.GroupTheory.Transfer

@[expose] public section

namespace Q2226800

universe u

variable {G : Type u} [Group G]

/-- The Schur-Zassenhaus theorem, stated using a left complement. -/
theorem schur_zassenhaus_statement {N : Subgroup G} [N.Normal]
    (hN : Nat.Coprime (Nat.card N) N.index) :
    ∃ H : Subgroup G, Subgroup.IsComplement' H N := sorry

end Q2226800
