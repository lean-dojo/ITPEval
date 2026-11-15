-- Statement-only formalization of Thousand Theorems artifact Q1568811
-- (thousand-theorems__lean4__Q1568811), "Hahn decomposition theorem": every
-- signed measure admits complementary measurable positive and negative sets.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.VectorMeasure.Basic

@[expose] public section

open scoped MeasureTheory

namespace MeasureTheory.SignedMeasure.Q1568811

variable {α : Type*} [MeasurableSpace α]

/-- The Hahn decomposition theorem for a signed measure. -/
theorem hahn_decomposition_theorem (s : SignedMeasure α) :
    ∃ i j : Set α, MeasurableSet i ∧ 0 ≤[i] s ∧ MeasurableSet j ∧ s ≤[j] 0 ∧ IsCompl i j :=
  sorry

end MeasureTheory.SignedMeasure.Q1568811
