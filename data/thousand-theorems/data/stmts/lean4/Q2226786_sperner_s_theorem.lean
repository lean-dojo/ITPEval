-- Statement-only formalization of Thousand Theorems artifact Q2226786
-- (thousand-theorems__lean4__Q2226786), "Sperner's theorem": the cardinality
-- of any antichain of finite subsets of a finite type is at most the middle
-- binomial coefficient. This file contains no proof.

module

public import Mathlib.Combinatorics.SetFamily.LYM

@[expose] public section

namespace Q2226786

variable {α : Type*} [Fintype α] {𝒜 : Finset (Finset α)}

/-- Sperner's theorem for an antichain of finite subsets of a finite type. -/
theorem sperner_theorem_statement
    (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := sorry

end Q2226786
