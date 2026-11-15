-- Statement-only formalization of Thousand Theorems artifact Q288465
-- (thousand-theorems__lean4__Q288465), "Orbit-stabilizer theorem": for any group
-- action and point, the point's orbit is equivalent to the acting group modulo
-- the point's stabilizer. This file contains no proof.

module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section

universe u v

namespace Q288465

variable {β : Type v}

/-- The orbit of a point is equivalent to the acting group modulo its stabilizer. -/
noncomputable def orbitEquivQuotientStabilizer_statement
    (α : Type u) [Group α] [MulAction α β] (b : β) :
    MulAction.orbit α b ≃ α ⧸ MulAction.stabilizer α b := sorry

end Q288465
