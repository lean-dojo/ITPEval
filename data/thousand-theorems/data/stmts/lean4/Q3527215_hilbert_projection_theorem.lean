-- Statement-only formalization of Thousand Theorems artifact Q3527215
-- (thousand-theorems__lean4__Q3527215), "Hilbert projection theorem": every point
-- in a real inner product space has a nearest point in any nonempty complete convex set.
-- This file contains no proof.

module

public import Mathlib.Analysis.InnerProductSpace.Defs

public section

namespace Q3527215

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A nonempty complete convex set contains a point attaining the infimum of the distance
from any point in the ambient real inner product space. -/
theorem exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty)
    (h₁ : IsComplete K) (h₂ : Convex ℝ K) :
    ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := sorry

end Q3527215
