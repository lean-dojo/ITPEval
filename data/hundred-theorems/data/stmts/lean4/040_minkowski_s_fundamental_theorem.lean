/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

* `exists_pair_mem_lattice_not_disjoint_vadd`: Blichfeldt's principle, existence of two distinct
  points in a subgroup such that the translates of a set by these two points are not disjoint when
  the covolume of the subgroup is larger than the volume of the set.
* `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`: Minkowski's theorem, existence of
  a non-zero lattice point inside a convex symmetric domain of large enough volume.

## TODO

* Calculate the volume of the fundamental domain of a finite index subgroup
* Voronoi diagrams
* See [Pete L. Clark, *Abstract Geometry of Numbers: Linear Forms* (arXiv)](https://arxiv.org/abs/1405.2119)
  for some more ideas.

## References

* [Pete L. Clark, *Geometry of Numbers with Applications to Number Theory*][clark_gon] p.28
-/

public section


namespace MeasureTheory

open ENNReal Module MeasureTheory MeasureTheory.Measure Set Filter

open scoped Pointwise NNReal

variable {E L : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E}

/-- **Blichfeldt's Theorem**. If the volume of the set `s` is larger than the covolume of the
countable subgroup `L` of `E`, then there exist two distinct points `x, y ∈ L` such that `(x + s)`
and `(y + s)` are not disjoint. -/
theorem exists_pair_mem_lattice_not_disjoint_vadd [AddGroup L] [Countable L] [AddAction L E]
    [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by sorry
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]
    {L : AddSubgroup E} [Countable L] (fund : IsAddFundamentalDomain L F μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h : μ F * 2 ^ finrank ℝ E < μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s := by sorry
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [IsAddHaarMeasure μ]
    {L : AddSubgroup E} [Countable L] [DiscreteTopology L] (fund : IsAddFundamentalDomain L F μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : μ F * 2 ^ finrank ℝ E ≤ μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s := by sorry
end MeasureTheory
