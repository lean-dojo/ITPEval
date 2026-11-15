-- Statement-only formalization of Thousand Theorems artifact Q842953
-- (thousand-theorems__lean4__Q842953), "Lebesgue's density theorem": in a
-- second-countable metric Borel space with the Besicovitch covering property,
-- almost every point of an arbitrary set is a density point for that set.
-- This file contains no proof.

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Covering.VitaliFamily
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

open Fin Metric Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal MeasureTheory Topology

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

namespace Q842953

variable {β : Type*} [MetricSpace β] [MeasurableSpace β] [BorelSpace β]
  [SecondCountableTopology β] [HasBesicovitchCovering β]

/-- Lebesgue's density theorem for an arbitrary set in a Besicovitch metric space. -/
theorem lebesgue_density_theorem (μ : Measure β) [IsLocallyFiniteMeasure μ] (s : Set β) :
    ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
        (𝓝[>] 0) (𝓝 1) := sorry

end Q842953
