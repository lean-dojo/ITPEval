-- Statement-only formalization of Thousand Theorems artifact Q1032886
-- (thousand-theorems__lean4__Q1032886), "Hales–Jewett theorem": for every
-- finite alphabet and finite color type, some finite-dimensional word space
-- has a monochromatic combinatorial line under every coloring. This file
-- contains no proof.

module

public import Mathlib.Combinatorics.HalesJewett

@[expose] public section

universe u v

namespace Q1032886

/-- The Hales–Jewett theorem for arbitrary finite alphabet and color types. -/
theorem hales_jewett_statement (α : Type u) [Finite α] (κ : Type v) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ,
      ∃ l : Combinatorics.Line α ι, l.IsMono C := sorry

end Q1032886
