-- Statement-only formalization of Thousand Theorems artifact Q609612
-- (thousand-theorems__lean4__Q609612), "Knaster–Tarski theorem": the fixed points of a
-- monotone self-map of a complete lattice themselves form a complete lattice. This file
-- contains no proof.

module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Hom.Order

@[expose] public section

universe u

open Function

namespace Q609612

variable {α : Type u} [CompleteLattice α]

/-- Every set of fixed points has a least upper bound and a greatest lower bound in the
inherited order. This is the order-theoretic content of the Knaster-Tarski complete-lattice
instance. -/
theorem knasterTarskiCompleteLattice (f : α →o α) :
    ∀ S : Set (fixedPoints f),
      (∃ u : fixedPoints f, IsLUB S u) ∧
        ∃ l : fixedPoints f, IsGLB S l := sorry

end Q609612
