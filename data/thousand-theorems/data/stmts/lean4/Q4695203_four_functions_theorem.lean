-- Statement-only formalization of Thousand Theorems artifact Q4695203
-- (thousand-theorems__lean4__Q4695203), "Four functions theorem": four
-- nonnegative functions on a distributive lattice satisfying the pointwise
-- meet-join inequality satisfy the corresponding finite-family sum inequality.
-- This file contains no proof.

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Finset.Sups
public import Mathlib.Order.Sublattice

@[expose] public section

open Finset
open scoped FinsetFamily

namespace Q4695203

variable {α β : Type*}
variable [DistribLattice α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β]
  [ExistsAddOfLE β]

/-- The Ahlswede-Daykin four functions inequality for finite families in a
distributive lattice. -/
theorem four_functions_theorem [DecidableEq α] (f₁ f₂ f₃ f₄ : α → β)
    (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)) (s t : Finset α) :
    (∑ a ∈ s, f₁ a) * ∑ a ∈ t, f₂ a ≤
      (∑ a ∈ s ⊼ t, f₃ a) * ∑ a ∈ s ⊻ t, f₄ a := sorry

end Q4695203
