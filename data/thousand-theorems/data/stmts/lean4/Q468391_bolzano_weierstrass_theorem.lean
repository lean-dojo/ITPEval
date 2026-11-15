-- Statement-only formalization of Thousand Theorems artifact Q468391
-- (thousand-theorems__lean4__Q468391), "Bolzano–Weierstrass theorem": in a proper
-- pseudometric space, every sequence that is frequently in a bounded set has a
-- strictly monotone subsequence converging to a point in the set's closure; in
-- particular, this holds when every term lies in the set. This file contains no proof.

module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open Filter Bornology Metric
open scoped Topology

universe u

namespace Q468391

variable {X : Type u} [PseudoMetricSpace X] [ProperSpace X] {s : Set X}

/-- Bolzano–Weierstrass for a sequence frequently contained in a bounded set. -/
theorem tendsto_subseq_of_frequently_bounded (hs : IsBounded s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := sorry

/-- Bolzano–Weierstrass for a sequence contained in a bounded set. -/
theorem tendsto_subseq_of_bounded (hs : IsBounded s) {x : ℕ → X}
    (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := sorry

end Q468391
