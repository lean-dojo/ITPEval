-- Statement-only formalization of Thousand Theorems artifact Q537618
-- (thousand-theorems__lean4__Q537618), "Banach–Alaoglu theorem": the polar of
-- any neighborhood of zero in a seminormed vector space over a proper
-- nontrivially normed field is compact in the weak-star topology. This file contains no proof.

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

open Filter
open scoped Topology

namespace Q537618

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The polar of a subset of the seminormed vector space. -/
def polar (𝕜 : Type*) {E : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (s : Set E) : Set (WeakDual 𝕜 E) :=
  {f | ∀ x ∈ s, ‖f x‖ ≤ 1}

/-- The Banach–Alaoglu compactness theorem for polars of neighborhoods of zero. -/
theorem banach_alaoglu_theorem [ProperSpace 𝕜] {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsCompact (polar 𝕜 s) := sorry

end Q537618
