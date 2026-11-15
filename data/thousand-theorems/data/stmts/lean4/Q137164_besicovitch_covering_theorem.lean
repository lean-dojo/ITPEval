-- Statement-only formalization of Thousand Theorems artifact Q137164
-- (thousand-theorems__lean4__Q137164), "Besicovitch covering theorem": in a
-- second-countable metric space with the Besicovitch covering property, admissible closed balls
-- contain a countable pairwise-disjoint subfamily covering a set almost everywhere.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

open Fin Metric Set MeasureTheory

/-- A satellite configuration of `N + 1` balls with parameter `τ`. -/
structure Besicovitch.SatelliteConfig (α : Type*) [MetricSpace α] (N : ℕ) (τ : ℝ) where
  c : Fin N.succ → α
  r : Fin N.succ → ℝ
  rpos : ∀ i, 0 < r i
  h : Pairwise fun i j =>
    r i ≤ dist (c i) (c j) ∧ r j ≤ τ * r i ∨ r j ≤ dist (c j) (c i) ∧ r i ≤ τ * r j
  hlast : ∀ i < last N, r i ≤ dist (c i) (c (last N)) ∧ r (last N) ≤ τ * r i
  inter : ∀ i < last N, dist (c i) (c (last N)) ≤ r i + r (last N)

/-- The metric space excludes sufficiently large satellite configurations. -/
class HasBesicovitchCovering (α : Type*) [MetricSpace α] : Prop where
  no_satelliteConfig : ∃ (N : ℕ) (τ : ℝ), 1 < τ ∧
    IsEmpty (Besicovitch.SatelliteConfig α N τ)

namespace Q137164

variable {α : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α]
  [OpensMeasurableSpace α] [HasBesicovitchCovering α]

/-- A countable pairwise-disjoint family of admissible closed balls covers `s` almost everywhere. -/
theorem exists_disjoint_closedBall_covering_ae (μ : Measure α) [SFinite μ]
    (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) (R : α → ℝ)
    (hR : ∀ x ∈ s, 0 < R x) :
    ∃ (t : Set α) (r : α → ℝ), t.Countable ∧ t ⊆ s ∧
      (∀ x ∈ t, r x ∈ f x ∩ Ioo 0 (R x)) ∧
        μ (s \ ⋃ x ∈ t, closedBall x (r x)) = 0 ∧
          t.PairwiseDisjoint fun x => closedBall x (r x) := sorry

end Q137164
