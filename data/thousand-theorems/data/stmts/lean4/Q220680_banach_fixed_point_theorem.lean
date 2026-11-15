-- Statement-only formalization of Thousand Theorems artifact Q220680
-- (thousand-theorems__lean4__Q220680), "Banach fixed-point theorem": a contraction on
-- a complete extended metric space has a fixed point approached by its iterates with an
-- explicit geometric error bound. This file contains no proof.

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Dynamics.FixedPoints.Topology
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

open NNReal Topology ENNReal Filter Function

variable {α : Type*}

namespace Q220680

/-- A map is contracting with constant `K` when `K < 1` and it is `K`-Lipschitz. -/
def ContractingWith [EMetricSpace α] (K : ℝ≥0) (f : α → α) :=
  K < 1 ∧ LipschitzWith K f

open EMetric Set

/-- Banach's fixed-point theorem with convergence and an explicit error estimate. -/
theorem exists_fixedPoint [EMetricSpace α] [CompleteSpace α] {K : ℝ≥0} {f : α → α}
    (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) :
    ∃ y, IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) := sorry

end Q220680
