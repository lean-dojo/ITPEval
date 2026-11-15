-- Statement-only formalization of Thousand Theorems artifact Q967972
-- (thousand-theorems__lean4__Q967972), "Open mapping theorem (complex analysis)":
-- an analytic complex-valued function on a preconnected set is constant there or maps
-- every open subset of that set to an open set. This file contains no proof.

module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

open Set

-- Restore the canonical complex normed-field instances omitted by the reduced module graph.
noncomputable local instance : NormedField ℂ where
  dist_eq _ _ := rfl
  norm_mul := Complex.norm_mul

noncomputable local instance : NontriviallyNormedField ℂ where
  non_trivial := ⟨2, Complex.norm_two.symm ▸ one_lt_two⟩

namespace Q967972

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {U : Set E} {g : E → ℂ}

/-- The global open mapping dichotomy for an analytic complex-valued function on a
preconnected set. -/
theorem open_mapping_theorem_complex_analysis
    (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) :
    (∃ w, ∀ z ∈ U, g z = w) ∨ ∀ s ⊆ U, IsOpen s → IsOpen (g '' s) := sorry

end Q967972
