-- Statement-only formalization of Thousand Theorems artifact Q132427
-- (thousand-theorems__lean4__Q132427), "Rademacher's theorem": a function between
-- finite-dimensional real normed vector spaces that is Lipschitz on a measurable set is
-- differentiable within that set almost everywhere. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Convex.Body
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.MetricSpace.Lipschitz

public section

open Filter MeasureTheory Measure

namespace Q132427

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {C : NNReal} {f : E → F} {s : Set E} {μ : Measure E} [IsAddHaarMeasure μ]

/-- Rademacher's theorem for a function that is Lipschitz on a measurable set. -/
theorem rademacher_on_measurable_set (hf : LipschitzOnWith C f s) (hs : MeasurableSet s) :
    ∀ᵐ x ∂(μ.restrict s), DifferentiableWithinAt ℝ f s x := sorry

end Q132427
