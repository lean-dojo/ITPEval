-- Statement-only formalization of Thousand Theorems artifact Q3229352
-- (thousand-theorems__lean4__Q3229352), "Vitali covering theorem": a fine
-- family of closed sets satisfying a uniform measure comparison has a
-- countable disjoint subfamily covering the given set almost everywhere.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Covering.VitaliFamily
public import Mathlib.Data.Set.Pairwise.Lattice

@[expose] public section

variable {α ι : Type*}

open Set Metric MeasureTheory TopologicalSpace Filter
open scoped NNReal ENNReal Topology

namespace Q3229352

/-- The measurable Vitali covering theorem. -/
theorem vitali_covering_theorem
    [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (s : Set α) (t : Set ι) (C : ℝ≥0) (r : ι → ℝ) (c : ι → α)
    (B : ι → Set α) (hB : ∀ a ∈ t, B a ⊆ closedBall (c a) (r a))
    (μB : ∀ a ∈ t, μ (closedBall (c a) (3 * r a)) ≤ C * μ (B a))
    (ht : ∀ a ∈ t, (interior (B a)).Nonempty)
    (h't : ∀ a ∈ t, IsClosed (B a))
    (hf : ∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ a ∈ t, r a ≤ ε ∧ c a = x) :
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint B ∧
      μ (s \ ⋃ a ∈ u, B a) = 0 := sorry

end Q3229352
