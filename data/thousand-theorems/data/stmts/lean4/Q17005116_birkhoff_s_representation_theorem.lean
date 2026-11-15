-- Statement-only formalization of Thousand Theorems artifact Q17005116
-- (thousand-theorems__lean4__Q17005116), "Birkhoff's representation theorem":
-- the canonical map from a finite distributive lattice to the powerset of its
-- sup-irreducible elements is an injective lattice homomorphism. This file contains no proof.

module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Irreducible
public import Mathlib.Order.UpperLower.Closure

@[expose] public section

universe u

namespace Q17005116

variable {α : Type u} [DistribLattice α] [Fintype α] [@DecidablePred α SupIrred]

/-- The canonical Birkhoff map sends an element to the sup-irreducibles below it. -/
theorem birkhoffSet_statement :
    ∃ f : LatticeHom α (Set {a : α // SupIrred a}),
      Function.Injective f ∧ ∀ x a, a ∈ f x ↔ (a : α) ≤ x := sorry

end Q17005116
