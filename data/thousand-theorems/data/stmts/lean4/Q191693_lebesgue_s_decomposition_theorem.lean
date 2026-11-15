-- Statement-only formalization of Thousand Theorems artifact Q191693
-- (thousand-theorems__lean4__Q191693), "Lebesgue's decomposition theorem":
-- every s-finite measure has a decomposition relative to a sigma-finite measure into a
-- mutually singular measure and a measure given by a measurable density.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

@[expose] public section

namespace MeasureTheory.Measure.Q191693

variable {α : Type*} [MeasurableSpace α]

/-- Lebesgue's decomposition theorem for an s-finite and a sigma-finite measure. -/
theorem lebesgue_decomposition_theorem (μ ν : Measure α) [SFinite μ] [SigmaFinite ν] :
    HaveLebesgueDecomposition μ ν := sorry

end MeasureTheory.Measure.Q191693
