-- Statement-only formalization of Thousand Theorems artifact Q918099
-- (thousand-theorems__lean4__Q918099), "Ramsey's theorem": every finite coloring
-- of the fixed-cardinality subsets of an infinite subset of the natural numbers
-- has an infinite monochromatic subset. This file contains no proof.

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace Q918099

/-- The `r`-element finite subsets of a set. -/
@[reducible] def rset' (r : ℕ) {α : Type} (m : Set α) : Set (Finset α) :=
  {x | x.card = r ∧ ∀ t ∈ x, t ∈ m}

/-- Infinite Ramsey's theorem for colorings whose colors lie in a fixed finite set. -/
theorem ramsey_r {α : Type} (K : Finset α) {r : ℕ} {M₁ : Set ℕ}
    (hM₁ : M₁.Infinite) (c : Finset ℕ → α)
    (h : ∀ e ∈ rset' r M₁, c e ∈ K) :
    ∃ M₂ ⊆ M₁, M₂.Infinite ∧ ∃ col ∈ K, ∀ i ∈ rset' r M₂, c i = col := sorry

end Q918099
