-- Statement-only formalization of Thousand Theorems artifact Q1097021
-- (thousand-theorems__lean4__Q1097021), "Minkowski's theorem": a convex symmetric
-- set of sufficiently large Haar measure contains a nonzero point of a countable lattice.
-- This file contains no proof.

module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure

public section

open ENNReal Module MeasureTheory MeasureTheory.Measure Set Filter Function

open scoped Pointwise NNReal

namespace MeasureTheory

/-- A faithful reconstruction of the source predicate: the translates of the set are measurable,
cover almost everywhere, and are pairwise almost-everywhere disjoint. -/
structure IsAddFundamentalDomain (G : Type*) {α : Type*} [Zero G] [VAdd G α]
    [MeasurableSpace α] (s : Set α) (μ : Measure α) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ s
  protected aedisjoint : Pairwise <| (AEDisjoint μ on fun g : G => g +ᵥ s)

end MeasureTheory

namespace Q1097021

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E}

/-- The Minkowski convex body theorem. -/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]
    {L : AddSubgroup E} [Countable L] (fund : MeasureTheory.IsAddFundamentalDomain L F μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h : μ F * 2 ^ finrank ℝ E < μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s := sorry

end Q1097021
