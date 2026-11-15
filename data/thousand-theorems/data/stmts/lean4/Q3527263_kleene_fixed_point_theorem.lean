-- Statement-only formalization of Thousand Theorems artifact Q3527263
-- (thousand-theorems__lean4__Q3527263), "Kleene fixed-point theorem": for an
-- omega-Scott-continuous monotone self-map of a complete lattice, the least fixed point
-- is the supremum of its finite iterates from bottom. This file contains no proof.

module

public import Mathlib.Order.FixedPoints

@[expose] public section

universe u

open Function OmegaCompletePartialOrder

namespace Q3527263

variable {α : Type u} [CompleteLattice α]

/-- The least fixed point is the supremum of the finite iterates from bottom. -/
theorem kleene_fixed_point_theorem (f : α →o α) (h : ωScottContinuous f) :
    f.lfp = ⨆ n, f^[n] ⊥ := sorry

end Q3527263
