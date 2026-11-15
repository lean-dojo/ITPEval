-- Statement-only formalization of Thousand Theorems artifact Q2226677
-- (thousand-theorems__lean4__Q2226677), "Gelfand–Mazur theorem": a complete
-- complex normed ring whose nonzero elements are exactly its units is
-- algebra-equivalent to the complex numbers. This file contains no proof.

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section

-- Restore the canonical complex normed-field instance omitted by the reduced module graph.
noncomputable local instance : NormedField ℂ where
  dist_eq _ _ := rfl
  norm_mul := Complex.norm_mul

namespace Q2226677

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The Gelfand–Mazur algebra equivalence for a complete complex normed ring. -/
noncomputable def algEquivComplexOfComplete_statement
    (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) : ℂ ≃ₐ[ℂ] A := sorry

end Q2226677
