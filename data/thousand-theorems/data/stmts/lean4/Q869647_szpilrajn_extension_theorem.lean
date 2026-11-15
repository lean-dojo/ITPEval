-- Statement-only formalization of Thousand Theorems artifact Q869647
-- (thousand-theorems__lean4__Q869647), "Szpilrajn extension theorem": every partial
-- order relation on an arbitrary type extends to a linear order relation.
-- This file contains no proof.

module

public import Mathlib.Order.Zorn

@[expose] public section

namespace Q869647

universe u

/-- The Szpilrajn extension theorem for an arbitrary partial order relation. -/
theorem extend_partialOrder {α : Type u} (r : α → α → Prop) [IsPartialOrder α r] :
    ∃ s : α → α → Prop, IsLinearOrder α s ∧ r ≤ s := sorry

end Q869647
