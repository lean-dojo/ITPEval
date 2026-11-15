-- Statement-only formalization of Thousand Theorems artifact Q258374
-- (thousand-theorems__lean4__Q258374), "Carathéodory's theorem (measure theory)":
-- for every outer measure, the sets that split every test set additively form
-- a measurable space. This file contains no proof.

module

public import Mathlib.MeasureTheory.OuterMeasure.OfFunction
public import Mathlib.MeasureTheory.PiSystem

@[expose] public section

open Set

namespace MeasureTheory
namespace Q258374

universe u

/-- The sets satisfying Carathéodory's splitting criterion form a measurable space. -/
theorem caratheodory_theorem_statement {α : Type u} (m : OuterMeasure α) :
    ∃ M : MeasurableSpace α, ∀ s : Set α,
      MeasurableSet[M] s ↔ ∀ t : Set α, m t = m (t ∩ s) + m (t \ s) := sorry

end Q258374
end MeasureTheory
