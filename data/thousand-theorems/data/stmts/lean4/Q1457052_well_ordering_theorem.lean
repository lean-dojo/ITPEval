-- Statement-only formalization of Thousand Theorems artifact Q1457052
-- (thousand-theorems__lean4__Q1457052), "Well-ordering theorem": every type
-- admits a linear order whose strict order is well-founded.
-- This file contains no proof.

module

public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

universe u

namespace Q1457052

/-- The well-ordering theorem for an arbitrary type. -/
theorem exists_wellOrder_statement (α : Type u) :
    ∃ (_ : LinearOrder α), WellFoundedLT α := sorry

end Q1457052
