-- Statement-only formalization of Thousand Theorems artifact Q1191319
-- (thousand-theorems__lean4__Q1191319), "Radon–Nikodym theorem": under a
-- Lebesgue decomposition, absolute continuity of one measure with respect to another is
-- equivalent to recovering it by density with its Radon–Nikodym derivative.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

@[expose] public section

variable {α : Type*} {m : MeasurableSpace α}

namespace MeasureTheory.Measure.Q1191319

variable {μ ν : Measure α}

/-- The Radon–Nikodym theorem for measures admitting a Lebesgue decomposition. -/
theorem radon_nikodym_theorem [HaveLebesgueDecomposition μ ν] :
    μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ := sorry

end MeasureTheory.Measure.Q1191319
