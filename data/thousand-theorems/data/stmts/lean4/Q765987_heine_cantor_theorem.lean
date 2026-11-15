-- Statement-only formalization of Thousand Theorems artifact Q765987
-- (thousand-theorems__lean4__Q765987), "Heine–Cantor theorem": every continuous map
-- from a compact uniform space to a uniform space is uniformly continuous.
-- This file contains no proof.

module

public import Mathlib.Topology.UniformSpace.Compact

@[expose] public section

namespace Q765987

variable {α β : Type*} [UniformSpace α] [UniformSpace β]

/-- Heine–Cantor: a continuous map from a compact uniform space is uniformly continuous. -/
theorem heine_cantor [CompactSpace α] {f : α → β} (h : Continuous f) :
    UniformContinuous f := sorry

end Q765987
