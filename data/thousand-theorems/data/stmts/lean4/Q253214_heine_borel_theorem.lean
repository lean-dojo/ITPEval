-- Statement-only formalization of Thousand Theorems artifact Q253214
-- (thousand-theorems__lean4__Q253214), "Heine–Borel theorem": in a proper
-- Hausdorff pseudometric space, a set is compact if and only if it is closed
-- and bounded. This file contains no proof.

module

public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

universe u

namespace Q253214

variable {α : Type u} [PseudoMetricSpace α] [T2Space α] [ProperSpace α]

/-- The Heine–Borel compactness characterization for proper Hausdorff pseudometric spaces. -/
theorem heine_borel_theorem (s : Set α) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s := sorry

end Q253214
