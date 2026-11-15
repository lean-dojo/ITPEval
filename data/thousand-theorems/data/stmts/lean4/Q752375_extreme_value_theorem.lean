-- Statement-only formalization of Thousand Theorems artifact Q752375
-- (thousand-theorems__lean4__Q752375), "Extreme value theorem": a continuous
-- function on a nonempty compact set attains its minimum. This file contains no proof.

module

public import Mathlib.Topology.Order.Compact

@[expose] public section

namespace Q752375

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [TopologicalSpace β]

/-- The extreme value theorem: a continuous function attains its minimum on a compact set. -/
theorem extreme_value_theorem [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x := sorry

end Q752375
