-- Statement-only formalization of Thousand Theorems artifact Q1477053
-- (thousand-theorems__lean4__Q1477053), "Arzelà–Ascoli theorem": an equicontinuous
-- family of bounded continuous functions on a compact space, with values in a compact
-- subset of a Hausdorff pseudo-metric space, has compact closure. This file contains no proof.

module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.MetricSpace.Equicontinuity

@[expose] public section

open BoundedContinuousFunction Set Metric

universe u v

namespace Q1477053

variable {α : Type u} {β : Type v} [TopologicalSpace α] [CompactSpace α] [PseudoMetricSpace β]

/-- The Arzelà–Ascoli theorem for bounded continuous functions with compact range. -/
theorem arzela_ascoli_theorem_statement [T2Space β] (s : Set β) (hs : IsCompact s)
    (A : Set (α →ᵇ β)) (in_s : ∀ (f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s)
    (H : Equicontinuous ((↑) : A → α → β)) : IsCompact (closure A) := sorry

end Q1477053
