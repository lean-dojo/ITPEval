-- Statement-only formalization of Thousand Theorems artifact Q2525646
-- (thousand-theorems__lean4__Q2525646), "Jordan–Hölder theorem": in any
-- JordanHolderLattice, composition series with the same head and last element are equivalent.
-- This file contains no proof.

module

public import Mathlib.Order.JordanHolder

@[expose] public section

universe u

namespace Q2525646

/-- The Jordan–Hölder theorem for composition series in a Jordan–Hölder lattice. -/
theorem jordan_holder_statement {X : Type u} [Lattice X] [JordanHolderLattice X]
    (s₁ s₂ : CompositionSeries X) (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    CompositionSeries.Equivalent s₁ s₂ := sorry

end Q2525646
